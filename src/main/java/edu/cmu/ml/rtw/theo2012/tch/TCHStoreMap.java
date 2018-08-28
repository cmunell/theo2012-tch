package edu.cmu.ml.rtw.theo2012.tch;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.NoSuchElementException;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import com.google.common.base.Preconditions;
import com.google.common.collect.Lists;
import tokyocabinet.HDB;


import edu.cmu.ml.rtw.theo2012.core.*;
import edu.cmu.ml.rtw.util.FasterLRUCache;
import edu.cmu.ml.rtw.util.Logger;
import edu.cmu.ml.rtw.util.LogFactory;
import edu.cmu.ml.rtw.util.Properties;
import edu.cmu.ml.rtw.util.Timer;

/**
 * {@link StoreMap} implementation that uses a Tokyo Cabinet hash database as the underlying storage
 * mechanism.
 *
 * The location should name a file.  At present, the filename is passed to Tokyo Cabinet verbatim.
 * In the future, we may guarantee support for some URN-style things.
 *
 * Note that, as of this writing, this does not implement the full java.util.Map interface.  Only
 * those parts needed by {@link StringListStore} are implemented.  While it seems like a cool idea
 * to be able to have a drop-in Tokyo Cabinet based HashMap, parts of the interface are onerous
 * (e.g. the Map.Entry view of the container) considering what we need and what we have time to do.
 * So that's left for future work.
 *
 * Note that this maintains a write-back cache by default.  It can be very useful to disable the
 * cache when it won't be needed, such as when just writing entries without ever reading or
 * rewriting them, by passing a zero to {@link setCacheSize}.
 *
 * In order to ensure that modifications directly to the values in the map (i.e. without using
 * something like {@link put}) are not lost, this class must flush all cache entries to disk upon
 * being closed.  This may result in many spurious writes.  This behavior may be defeated through
 * the use of {@link setForceAlwaysDirty} when the caller is willing to gauarantee that
 * modifications will never be made except via {@link put}.
 */
public class TCHStoreMap implements StringListStoreMap {
    private final static Logger log = LogFactory.getLogger();
    private final ReentrantReadWriteLock rwl = new ReentrantReadWriteLock(true);
    private final Lock readLock = rwl.readLock();
    private final Lock writeLock = rwl.writeLock();

    /**
     * Database cache
     *
     * This caches RTWValues, so that we conserve time by not marshalling them into and out of their
     * native DB storage format.  Tokyo Cabinet offers caching abilities, and that's an option that
     * could use re-exploration some day, especially since this cache can incur noticable GC
     * overhead when it's not small (say 1k-10k).
     */
    protected class RTWValCache extends StringListStoreMapCache {
        private final ReentrantReadWriteLock crwl = new ReentrantReadWriteLock(true);
        private final Lock cReadLock = crwl.readLock();
        private final Lock cWriteLock = crwl.writeLock();
        protected final boolean writeInXML = false;

        public RTWValCache(int cacheSize, boolean writeBack, boolean readOnly,
                boolean forceAlwaysDirty) {
            super(cacheSize, writeBack, readOnly, forceAlwaysDirty);
        }

        @Override protected RTWListValue get(String key) {
            try {
                RTWListValue value = null;
                byte[] bytes;
                cReadLock.lock();
                try {
                    bytes = db.get(key.getBytes());
                } finally {
                    cReadLock.unlock();
                }
                if (bytes != null) {
                    boolean wantToUpdateExistingValue = false;

                    if (bytes.length < 1) {
                        log.error("Ignoring illegal empty value for key \"" + key + "\"");
                        value = null;
                        wantToUpdateExistingValue = true;
                    }

                    // This special case is for autoconverting the "0" value we put in the " " key
                    // until May 2012.  Ugly, but oh well.
                    else if (bytes.length == 1 && bytes[0] == '0') {
                        value = new RTWImmutableListValue(new RTWIntegerValue(0));
                        wantToUpdateExistingValue = true;
                    }

                    else {
                        // Use this method so that we can read either the old XML-format values or
                        // the new UTF8 ones.
                        RTWValue v = RTWValue.fromUTF8(bytes);
                        if (!(v instanceof RTWListValue)) {
                            if (v.asString().equals("NO_THEO_VALUE") || v.asString().equals("")) {
                                log.info("Treating explicit NO_THEO_VALUE as as empty slot for key "
                                        + key);
                                value = null;
                                wantToUpdateExistingValue = true;
                            } else {
                                value = new RTWImmutableListValue(v);
                                log.warn("Autoconverted non-list value " + v + " found for key " + key
                                        + " to " + value);
                                // bkdb 2014-11-13: ran into this with the 489 KB, and there isn't
                                // time for a reconversion.  In fact, this seems to be fully
                                // necessary for further conversions, although it would be nice if
                                // these kinds of special cases could be moved to somewhere else.
                                // Maybe a subclass used only by Theo2012Converter or something like
                                // that?
                                //
                                // bkdb 2014-11-15: In fact, this needs to be a separate step where
                                // all keys are autoconverted according to all of these rules (well,
                                // not all, but any KB old enough to trigger any of these special
                                // cases ought to go through the XML conversion and vise versa).
                                // Otherwise, slots that we eventually consider to be empty appear
                                // to exist, and then StringListStore will either tend to get into
                                // an infinite loop or throw an exception when trying to delete
                                // something that isn't there.  Preferable to impose an extra
                                // pre-cleaning step than keep making our modern, common case code
                                // more and more complicated.
                                //
                                // KbManipulation.ensureValueFormatting is meant to approximate a
                                // proper conversion by invoking this get method on every key in the
                                // store.  We never did get around to making pr-conceptification KBs
                                // work, but it seems like a good idea to retain all this kind of
                                // code that was meant to get us into a position of being able to.

                                // throw new RuntimeException("Non-list value " + v
                                // + " found for key " + key);
                                wantToUpdateExistingValue = true;
                            }
                        } else {
                            value = (RTWListValue)v;
                        }

                        // Proactively convert any XML value to a UTF8 one on sight (as long as
                        // we're not read-only)
                        if (bytes[0] == '<') wantToUpdateExistingValue = true;
                        
                        if (!readOnly && wantToUpdateExistingValue) {
                            cWriteLock.lock();
                            try {
                                if (value == null) db.out(key.getBytes());
                                else db.put(key.getBytes(), value.toUTF8());
                            } finally {
                                cWriteLock.unlock();
                            }
                        }
                    }
                }
                return value;
            } catch (Exception e) {
                throw new RuntimeException("get(\"" + key + "\")", e);
            }
        }

        @Override protected void put(String location, RTWListValue value, boolean mightMutate) {
            cWriteLock.lock();
            try {
                Preconditions.checkNotNull(db, "database is not open.");
                Preconditions.checkState(!readOnly, "Internal error: Should not have had a dirty entry to commit on a read-only KB");

                if (writeInXML) {
                    if (true) {
                        throw new RuntimeException("Writing KB records in XML not implemented");
                        // To do this properly, I suppose move the XML routines out of
                        // KbUtiltiy.java in the OntologlyLearner repository into a utility class in
                        // this repository.
                    } else {
                        // this is the original implementation
                        // db.put(location.getBytes(), KbUtility.RTWValueToXML(value).getBytes());
                    }
                } else {
                    db.put(location.getBytes(), value.toUTF8());
                }
            } catch (Exception e) {
                throw new RuntimeException("put(\"" + location + "\", " + value + ", " + mightMutate
                        + ")", e);
            } finally {
                cWriteLock.unlock();
            }
        }

        @Override protected void remove(String key) {
            cWriteLock.lock();
            try {
                Preconditions.checkNotNull(db, "database is not open.");
                Preconditions.checkState(!readOnly, "Internal error: Should not have had a dirty entry to commit on a read-only KB");
                
                db.out(key.getBytes());
            } finally {
                cWriteLock.unlock();
            }
        }
    }

    /**
     * Class we use to return an iterator over all Tokyo Cabinet keys
     *
     * Tokyo Cabinet only supports one iterator at a time, so having two of these in action
     * simultaneously should be guarded against.  To achieve this, we give TCHStoreMap an
     * activeIterator member, and have instances of this class throw an exception if activeIterator
     * isn't set to them.  That way, constructing a new KeyIterator invalidates all older
     * KeyIterator instances.
     */
    protected class KeyIterator implements Iterator<String> {
        protected String next = null;

        public KeyIterator() {
            // Make sure the database sees any modifications hanging out in the cache!
            if (kbCache != null) kbCache.commitAllDirty(true);
            else kbCacheTL.get().commitAllDirty(true);
            if (!db.iterinit()) throw new RuntimeException("iterinit failed"); 
            next = db.iternext2();
            TCHStoreMap.this.activeIterator = this;
        }

        @Override public boolean hasNext() {
            if (TCHStoreMap.this.activeIterator != this)
                throw new RuntimeException("This iterator has been invalidated (perhaps because a newer one has been constructed)");
            return (next != null);
        }

        @Override public synchronized String next() throws NoSuchElementException {
            if (TCHStoreMap.this.activeIterator != this)
                throw new RuntimeException("This iterator has been invalidated (perhaps because a newer one has been constructed)");
            if (next == null) throw new NoSuchElementException();
            String tmp = next;
            next = db.iternext2();
            return tmp;
        }

        @Override public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Class we use to present the keys of our DB as a read-only java.util.Set without actually
     * loading them all into RAM
     */
    protected class KeySet implements Set<String> {
        @Override public boolean add(String s) {
            throw new UnsupportedOperationException();
        }

        @Override public boolean addAll(Collection<? extends String> c) {
            throw new UnsupportedOperationException();
        }

        @Override public void clear() {
            throw new UnsupportedOperationException();
        }

        @Override public boolean contains(Object o) {
            if (!(o instanceof String)) return false;
            String key = (String)o;
            if (kbCache != null) return (kbCache.getValue(key) != null);
            else return (kbCacheTL.get().getValue(key) != null);
        }

        @Override public boolean containsAll(Collection<?> c) {
            for (Object o : c)
                if (!contains(o)) return false;
            return true;
        }

        @Override public boolean equals(Object o) {
            // Equality here is defined as o being a collection of Strings that is exactly equal to
            // our set of keys.  But I don't see as we need to exspend the effort to implement that.
            throw new RuntimeException("Not implemented");
        }
        
        @Override public int hashCode() {
            // Why would anybody need this?
            throw new RuntimeException("Not implemented");
        }

        @Override public boolean isEmpty() {
            return TCHStoreMap.this.isEmpty();
        }

        @Override public Iterator<String> iterator() {
            return new KeyIterator();
        }

        @Override public boolean remove(Object o) {
            throw new UnsupportedOperationException();
        }

        @Override public boolean removeAll(Collection<?> c) {
            throw new UnsupportedOperationException();
        }

        @Override public boolean retainAll(Collection<?> c) {
            throw new UnsupportedOperationException();
        }

        @Override public int size() {
            return TCHStoreMap.this.size();
        }

        @Override public Object[] toArray() {
            // Make sure we invalidate any currently-active iterators
            TCHStoreMap.this.activeIterator = null;

            int size = size();
            String[] ar = new String[size];
            if (!db.iterinit()) throw new RuntimeException("iterinit failed"); 
            for (int i = 0; i < size; i++)
                ar[i] = db.iternext2();
            return ar;
        }

        @Override public <T> T[] toArray(T[] a) {
            // Why would anybody need this?
            throw new RuntimeException("Not implemented");
        }
    }

    /**
     * Filename of the database (only valid when db != null)
     */
    protected String openDBLocation;

    /**
     * Whether or not we're in read-only mode
     */
    protected boolean readOnly;

    /**
     * System.currentTimeMillis at time we last acted on a large access hint
     */
    protected long lastLargeAccessHint = 0;

    /**
     * Properties
     *
     * We don't actually have properties yet.  // bk:prop
     */
    protected Properties properties;

    /**
     * The Database
     *
     * null when and only when no database is open
     *
     * It'd be debatably cleaner to sequester this within the cache in order to force coherency by
     * design, but then we'd have to go out of our way for operations other than the typical
     * get/put/delete, and the cache class would get cluttered.
     */
    protected HDB db;

    /**
     * Quick & dirty cache of KB entries stored as RTWValues to limit conversion to and from the
     * native database records, and excess pressure on underlying database
     */
    protected RTWValCache kbCache;

    /**
     * System by which we maintain one cache per thread in read-only mode.
     * 
     * bkisiel 2013-05-10: Doing this because synchronizing on the cache becomes a real bottleneck
     * for concurrent KB-heavy operations, and setting the cache size to zero is undesirable due to
     * the speed penalty.  I guess we'll find out if this ever produces memory footprint issues that
     * aren't curable through smaller cache sizes; it would be easy enough to make this optional.
     *
     * This is non-null only if we're using it.
     *
     * FODO: This might should move in to StringListStoreMapCache.
     */
    ThreadLocal<RTWValCache> kbCacheTL = null;

    // Parameter values for the construction of new RTWValCache instances
    int kbCacheSize;
    boolean writeBack;
    boolean forceAlwaysDirty;

    /**
     * Used by KeyIterator instances to ensure that only the most-recently-constructed KeyIterator
     * instance is usable.
     */
    protected KeyIterator activeIterator = null;

    // bkisiel 2010-02-24: This thing here is as far as I got in trying to get Matlab to be able to
    // use this Java stuff, run a "clear java", and then run more of this Java stuff, which would
    // enable it to see changes to the Java code without having to quit and restart.  The current
    // obsticle to doing that is the loading of the Tokyo Cabinet native libraries.  The code below
    // is taken from http://forums.sun.com/thread.jspa?threadID=633985 but the problem is that
    // apparently "tokyocabinet.HDB" is not the name it's looking for.  So rather than continue to
    // spin my wheels on this, I'm just going to suffer quits and restarts.
    //
    protected static HDB getNewHDB() {
        try {
            ClassLoader sysCL = TCHStoreMap.class.getClassLoader().getSystemClassLoader();
            Class cb = sysCL.loadClass("tokyocabinet.HDB");
            HDB hdb = (HDB)cb.newInstance();
            return hdb;
        } catch(ClassNotFoundException e) {
            throw new RuntimeException(e);
        } catch (InstantiationException e) {
            throw new RuntimeException(e);
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        }
    }

    public TCHStoreMap() {
        properties = TheoFactory.getProperties();

        /**
         * We used to be write-through in order to make things easier in terms of coherency with
         * slotlistCache.  May as well keep write-through mode around in case we need it for
         * debugging or some unexpected need.
         */
        writeBack = properties.getPropertyBooleanValue("kbCacheWriteBack", true);

        /*
         * bkisiel 2012-02-27: Still haven't retuned (or explored a dedicated slotlist cache) the in
         * the wake of all the different kinds of changes we've had to this format since its
         * inception.  But some recent speed investigations revealed a failure to be able to cache
         * conditionedKnownNegatives while doing relation instance iteration on the ongoing run's
         * KB.  While it's questionable to want to do that vs. having a dedicated cKN cache, it
         * seems generally prudent for the time being to be able to cover that kind of a case.
         * Kicking the size up to 100k took care of it.  What I haven't checked is if this incurs
         * too much CPU overhead on smaller KBs; it does not on this one I suppose we could try to
         * set this based on the KB size; for the record, this testing is being done on a KB with
         * 205B records (and with perhaps far too few buckets at 131M!)
         *
         * 2018-05: At NELL iteration 1106, shortly after moving to Theo2012, we wound up with
         * effectively intractably slow operation from the ConceptDeleter component for reasons that
         * are still not entirely clear but that are somehow related to garbage collection from
         * having to reload very large slots back in to the KB cache after a large number of
         * scattered reads/writes causing them to be dropped.  At this time, we explored cache size
         * settings to see what difference it might make.  It turns out that the traditional default
         * of 100k is reasonable; going much smaller quickly increases execution time, roughtly
         * doubling it by 10k.  There is maybe 10% more speed to be had at 1M, although memory use
         * from the cache is expectably some multiple larger, making it an appropriate tradeoff only
         * when there is RAM to spare.  Going larger didn't yield speed gains, and it looked like
         * there might even be speed decrease beyond 10M, probably owing to reduced RAM locality and
         * more memory management overhead.
         */
        kbCacheSize = properties.getPropertyIntegerValue("kbCacheSize", 100000);

        forceAlwaysDirty = true;
    }

    ////////////////////////////////////////////////////////////////////////////
    // Stuff that's not part of java.util.Map
    ////////////////////////////////////////////////////////////////////////////

    @Override public void open(String filename, boolean openInReadOnlyMode) {
        writeLock.lock();
        try {
            Preconditions.checkNotNull(filename);
            Preconditions.checkState(db == null, "close open DB beore calling setDbFilePath");
            readOnly = openInReadOnlyMode;

            File f = new File(filename);
            if (openInReadOnlyMode) {
                Preconditions.checkArgument(f.exists(), "KB does not exist: %s", filename);
                Preconditions.checkArgument(f.isFile(), "KB is not a file: %s", filename);
            }
            f = null;

            db = new HDB();

            // bkisiel 2010-03-18: These are my observations from playing with Tokyo Cabinet's
            // parameters:
            //
            // I observed a very high percentage of time going to "system" rather than "user" when
            // doing lots of fwmkeys calls.  I was able to abate this (and speed things way up) by
            // using a larger value for setxmsiz.  The default is 64MB.  I got best results setting
            // it to about the size of the DB.  I'm guessing this parameter controls some kind of
            // window size used to access the content of the DB file.  Reading in all DB keys
            // appears to cause maybe the entire DB to be read, and so it would make sense that
            // being able to keep the entire DB in ram through this window would speed up fwmkeys.
            // I'm guessing that "system" time is burnned by the OS/kernel copying back and forth
            // between FS cache and this window.
            //
            // I have yet to look into how the window size affects ordinary operations.  I'm looking
            // out for nontrivial "system" time as an indicator of a reasonable test case to use.
            //
            // If I'm reading the TC documentation right, the default setcache setting is 0, i.e. no
            // caching.  A friend of Andy's reported getting great speed with larger cache size
            // (albeit this was on a B+tree database), but I couldn't get consistently better
            // performance through this caching mechanism.  Maybe we just spend too little time in
            // TC.
            //
            // I want to say that using db.putasync instead of db.put does some combination of
            // speeding things up and making speed less sensitive to system load, but I couldn't
            // quite show that consistently and repeatably.  I'd go ahead and use putasync anyway,
            // but it seems more valuable for now to have put operations remain synchronous because
            // that should help with debugging situations where the system crashes and might not
            // have had the chance to flush the pending puts.  I'm thinking that we need the right
            // test case here as well -- our writes are probably pretty piecemeal and scattered
            // through time.
            //
            // Update 2010-03-21: Trying to run the 67th iteration on nell was too memory-intensive,
            // and everything hung on disk access, seemingly because the OS was reluctant to buffer
            // the 3 copies of the database vs. caching a bunch of seemingly-unused JVM vsize.
            // Bumping setxmsiz up to 512MB did help substantially by forcing the OS to buffer more
            // of the DBs, but ultimately still left things mostly blocking on disk reads.  Using
            // setcache had no significant effect.  It's tempting to set a larger setxmsiz by
            // default to improve resiliance toward memory starvation and try to keep things
            // smoother under load, but this testcase is too extreme to generalize from, I think.
            //
            // A database that has been optimized does speed things up noticably, and so far costs
            // something like 15 seconds.  So I have added that as something to be done just prior
            // to closing when the DB is not open in read-only mode, on the assumption that things
            // that write to the DB are typically long-running and will not be bothered by the extra
            // time spent.  We can of course make this optional if need be.

            // Number of buckets chosen to be the next order of magnitude smaller than the NELL KB
            // at iteration 650ish.  The KB gets optimized with more a more intelligent bucket
            // setting once per iteration, so this shouldn't be entirely unreasonable.
            //
            // 2012-12-21: Took the number of buckets down an order of magnitude so that an empty KB
            // is more like 750MB than 7.5 GB.  Might should take it down another notch?  I guess
            // the question is how likely it is to take an empty KB and make it as big as a "real"
            // KB without going through the process of automatically adjusting the number of bucket.
            // I suppose if the need is sufficent that we could have the optimization become
            // automatic on the fly when the number of keys exceeds the number of buckets by a
            // certain factor.
            db.tune(100000000, -1, -1, HDB.TLARGE); 

            boolean status;
            if (openInReadOnlyMode) status = db.open(filename, HDB.OREADER);
            else status = db.open(filename, HDB.OWRITER | HDB.OCREAT);
            if (!status) {
                int ecode = db.ecode();
                throw new RuntimeException("failed to open database: " + HDB.errmsg(ecode));
            }

            openDBLocation = filename;
            if (openInReadOnlyMode) {
                kbCache = null;
                kbCacheTL = new ThreadLocal() {
                    protected synchronized Object initialValue() {
                        return new RTWValCache(kbCacheSize, writeBack, readOnly, forceAlwaysDirty);
                    }
                };
                kbCacheTL.get().resize(kbCacheSize);
            } else {
                kbCache = new RTWValCache(kbCacheSize, writeBack, readOnly, forceAlwaysDirty);
                kbCache.resize(kbCacheSize);
            }

            // Backward compatability: before we switched to using StringListStoreBase, we stored a
            // plain String value in the " " slot.  Here we swap that out for an RTWListValue whose
            // first element is an RTWIntegerValue containing the corresponding value so that
            // nothing breaks when StringListStoreBase wants to check this value to see if the
            // slotlist cache exists.
            //
            // FODO: proper "magic bytes" stuff, etc.  Also coordination of us having our magic
            // bytes vs. them having theirs.  See similar note in TCHSuperStore
            String signal = db.get(" ");
            if (signal != null) {
                if (signal.equals("0"))
                    if (!readOnly)
                        put(" ", new RTWImmutableListValue(new RTWIntegerValue(0)));
                // Otherwise, it will blow up later.  We "should" detect that here and generate an
                // informative error message, but we've never written anything other than "0" here,
                // so the user has to be working with somebody else's TC database or something, and
                // that's going to make everything and anything blow up in strange ways.
            }
        } catch (Exception e) {
            throw new RuntimeException("open(\"" + filename + "\", " + openInReadOnlyMode + ")", e);
        } finally {
            writeLock.unlock();
        }
    }

    @Override public void close() {
        writeLock.lock();
        try {
            Preconditions.checkState(db != null, "DB is not open");
            flush(true);
            if (!db.close()) {
                int ecode = db.ecode();
                log.error("close error: " + HDB.errmsg(ecode));
            }
            openDBLocation = null;
            db = null;
            if (kbCache != null) kbCache.clear();
            if (kbCacheTL != null) kbCacheTL.get().clear();
            activeIterator = null;
        } finally {
            writeLock.unlock();
        }
    }

    @Override public String getLocation() {
        readLock.lock();
        try {
            if (db == null) return null;
            return openDBLocation;
        } finally {
            readLock.unlock();
        }
    }

    @Override public boolean isReadOnly() {
        readLock.lock();
        try {
            Preconditions.checkState(db != null, "Database not open.");
            return readOnly;
        } finally {
            readLock.unlock();
        }
    }

    @Override public void flush(boolean sync) {
        writeLock.lock();
        try {
            // TODO: move logging into the flush method and have it auto-log if more than, say, 200ms go by
            if (!readOnly) log.info("Flushing TCH cache...");
            if (kbCache != null) kbCache.clear();
            if (kbCacheTL != null) kbCacheTL.get().clear();
            if (sync) db.sync();
            if (!readOnly) log.info("Done flushing.");
        } finally {
            writeLock.unlock();
        }
    }

    @Override public void copy(String filename) {
        readLock.lock();
        try {
            Preconditions.checkState(db != null, "database is not open.");
            Preconditions.checkNotNull(filename);

            if (!db.copy(filename)) {
                // 2012-01: I don't see why this should ever happen, but it did once.  On the off chance
                // that it wasn't some strange matter of rebuilding classes while the JVM was still
                // loading them or something like that, I'd like to give another shot to trying to get
                // some kind of error code out of the situation.
                //
                // No exception in this case because a copy to /dev/null has no end-result anyway, and
                // is used only for the side-effect of pulling the database file into the OS page cache.
                if (filename.equals("/dev/null")) {
                    log.error("Error copying DB to /dev/null, ecode=" + db.ecode() + ", msg="
                            + db.errmsg());
                } else {
                    // db doesn't report an error code in this case
                    throw new RuntimeException("Error copying DB to \"" + filename + "\"");
                }
            }
        } finally {
            readLock.unlock();
        }
    }

    /**
     * Give a hint that you're about to access a large portion of this map
     *
     * When accessing a large portion of the the map (vs. small / casual / sporadic access),
     * reasonable performance depends on getting most or all of the TCH file into the OS's
     * filesystem cache.  Getting it in there can be done ~100x faster through a massive sequential
     * read.  So, before a large iteration or something of that sort, calling this will produce a
     * net speedup.
     */
    @Override public void giveLargeAccessHint() {
        readLock.lock();
        try {
            // No-op if not open
            if (db == null) return;

            // We could do this only once and then hope that the TCH file isn't kicked out of the cache
            // ever afterward, but we'll see what happens if we don't.  My thinking is that this
            // operation should take but a moment if the TCH file is in fact in the cache.
            //
            // Presumably, this will be very hard on a system that can't keep the entire TCH file in
            // RAM.  But how close can such a system be to gasping and choking anyway?  We can change
            // this policy as needed.
            //
            // Some use cases have us doing this more than we'd really want to.  As a crude saftey
            // mechanism against hints that come too often from over-eager signalling or from
            // hapenstatnce, I'm going to restrict a pull into the page cache to once every 10 minutes.
            // My guess is that if doing this repeatedly every 10 minutes is going to make a difference
            // to performance, then the computer is really getting hammered anyway, and trying to trying
            // to keep the file in RAM is at best not going to be very helpful.

            long now = System.currentTimeMillis();
            if (now - lastLargeAccessHint < 10*60*1000) {
                log.debug("Ignoring large access hint because we re-read " + getLocation()
                        + " less than 10 minutes ago.");
            } else {
                log.debug("Pulling " + getLocation() + " into OS page cache...");
                copy("/dev/null");
                lastLargeAccessHint = System.currentTimeMillis();
            }
        } finally {
            readLock.unlock();
        }
    }

    @Override public void logStats() {
        readLock.lock();
        try {
            if (kbCache != null) kbCache.logStats();
            if (kbCacheTL != null) kbCacheTL.get().logStats();
        } finally {
            readLock.unlock();
        }
    }

    @Override public void optimize() {
        writeLock.lock();
        try {
            if (readOnly)
                throw new RuntimeException("Cannot optimize when in read-only mode");
            log.info("Optimizing DB...");
            Timer t = new Timer();
            t.start();

            // Tokyo Cabinet's optimize routine works by creating a new, optimized copy of the DB file
            // alongside the existing DB file, then deletes the existing DB file and renames the
            // temporary copy.  So you could get as much as a doubling of space requirements along the
            // way, and that can be a problem when the DB file is sitting in a RAM drive or some other
            // small, special-purpose thing like that.  So we have an optional optimizeKbFilePath
            // parameter that specifies a secondary location to use for this process.
            //
            // Then the problem becomes getting Tokyo Cabinet to use this secondary location.  It turns
            // out that one can play some tricks with symlinks to do this, but that turs out to be
            // failure-prone, particularly when it comes to relative paths.
            //
            // Fortunately, it turns out that running something like "tchmgr list -pv src.tch | tchmgr
            // importtsv dst.tch" creates a dst.tch that is an optimized vesion of src.tch, and you have
            // full control over the two DB file locations.  Simply running that commandline is
            // failure-prone in that it will get tripped up by keys that contain tab characters or
            // newlines in the record values.  So we do the equivalent of that operation manually here,
            // and quite possibly save on time that would be spent rendering and parsing the TSV.
            //
            // As it happens, the implementation below does not seem to be as fast as using tchmgr.
            // Maybe because it's not split into two threads?  It's certainly not I/O-bound.  Anyway,
            // it's not too terribly bad, and we can opt to reinvestigate later on if we specifically
            // want to spend time making NELL faster.
            //
            // And there is one more subtlety here.  The difficulty that Tokyo Cabinet hash DBs present
            // to a storage mechanism is of scattered small writes with horrid locality -- something
            // that is an efficienty problem even for RAM (relatively speaking).  It's pathologically
            // bad for common cases like a RAID5 or RAID6 array to the point of being able to cripple
            // the array and keep it that way for hours.  Now, if optimizeKbFilePath has been specified,
            // then our underlying assumption is that it specifies a location that is somehow less
            // desirable than workingKbFilePath.  So, if we had to choose one to be subjected to these
            // scattered writes, then it would be workingKbFilePath.  Therefore, we first copy the DB
            // file to optimizeKbFilePath, and then read that copy and write the new optimized copy to
            // workingKbFilePath.  That way, optimizeKbFilePath is subjected to the relatively easy and
            // efficient case of a big, sequential write -- something not at all pathological for a
            // RADI5 or RAID6 array -- and then only has to cope with a big, sequential read, and now
            // there's even a chance that we'll be reading from the OS's cache instead of hitting the
            // underlying storage device.  In practice, the benefit from doing things this way can be
            // collossal.

            String workingKbFilePath = getLocation();
            String optimizeKbFilePath = properties.getProperty("optimizeKbFilePath", null);
            if (optimizeKbFilePath == null) {
                // Oh, well.  All we can do is let the chips fall where they may.
                if (!db.optimize())
                    throw new RuntimeException("Optimization failed!  KB corrupt now?");
            } else {
                close();
                Path workingPath = Paths.get(workingKbFilePath);
                Path optimizePath = Paths.get(optimizeKbFilePath);
                Files.deleteIfExists(optimizePath);
                Files.move(workingPath, optimizePath);

                HDB src = new HDB();
                HDB dst = new HDB();

                // Here, we must make sure to put eough buckets in dst or else the bucket setting
                // originally set by our open method will be lost.  While 100B buckets was "way more
                // than enough" when we first started using Tokyo Cabinet, we find circa iteration 500
                // that we wind up with somewhat more than 200B records.  The Tokyo Cabinet
                // documentation suggests using .5x to 4x as many buckets as records.  It's not clear
                // that moving up to 100B from the ~130k default produced the kind of speedups we were
                // expecting, so let's shoot for 500B buckets given 200B records.
                //
                // Now, here's the part where we cheat and know that, at present (2012-03), NELL
                // optimizes its DB on each iteration after blowing away all concepts, meaning that we
                // need to over-project the number of buckets to use here if we're basing it off of the
                // number of records.  It turns out that the ~200B-record database was about 50B at time
                // of optimization, so we'll set the bucket size to be 10x the number of records.  We
                // can always come back and make this something more tame if this results in
                // objectionably-large DBs for small KBs.  It doesn't seem to lead to much of any
                // speedup, anyway, which perhaps is worth further investigation.

                // bkisiel 2012-09-07: We've hit some very strange case where Tokyo Cabinet gets hung up
                // (largely in system time) on a get operation for a certain key and never returns.
                // This happens while executing CRC's or CRU's TCF.  It turns out that setting
                // HDB.TLARGE fixes this, which seems consistent with earlier findings suggesting that
                // moving from a record alignment of 16 to 32 worked similarly.

                if (!src.open(optimizeKbFilePath, HDB.OREADER))
                    throw new RuntimeException("Error opening " + optimizeKbFilePath + " for reading: "
                            + src.errmsg());
                long numBuckets = src.rnum() * 10L;
                dst.tune(numBuckets, -1, -1, HDB.TLARGE);
                if (!dst.open(workingKbFilePath, HDB.OWRITER | HDB.OCREAT))
                    throw new RuntimeException("Error opening " + workingKbFilePath + " for writing: "
                            + dst.errmsg());
                if (!src.iterinit())
                    throw new RuntimeException("Error from iterinit on " + optimizeKbFilePath + ": "
                            + src.errmsg());

                // Before we begin, give src the "large access hint".  For whatever reason, in practise,
                // the mv command alone doesn't always leave the KB sitting in the page cache, and that,
                // of course, makes a very big difference the speed of this operation.
                src.copy("/dev/null");

                while (true) {
                    byte[] key = src.iternext();
                    if (key == null) break;
                    dst.put(key, src.get(key));
                }
                dst.close();
                src.close();

                Files.delete(optimizePath);

                open(workingKbFilePath, false);
            }

            log.info("Optimization took " + t.getElapsedTimeFracHr());
        } catch (Exception e) {
            throw new RuntimeException("optimize()", e);
        } finally {
            writeLock.unlock();
        }
    }

    public int getCacheSize() {
        return kbCacheSize;
    }

    public void setCacheSize(int size) {
        writeLock.lock();
        try {
            kbCacheSize = size;
            if (kbCache != null) kbCache.resize(size);
            if (kbCacheTL != null) kbCacheTL.get().resize(size);
        } finally {
            writeLock.unlock();
        }
    }

    /**
     * Control the dirtiness assumptions about cached values
     *
     * As mentioned in the class comments, this class by default must assume that all entries in the
     * cache are dirty beacuse the calling code could modify the value objects without signalling
     * anything about it to the cache.  Of course, this can be expected to result in many spurious
     * writes.
     *
     * If the forceAlwaysDirty parameter is turned off, then this class will only consider cached
     * values to be dirty when they are modified through methods of this class such as {@link put}.
     * The onus, then, is on the calling code to ensure that values are never modified directly, as
     * changes in that case might be lost.
     */
    public void setForceAlwaysDirty(boolean forceAlwaysDirty) {
        writeLock.lock();
        try {
            this.forceAlwaysDirty = forceAlwaysDirty;
            if (kbCache != null) kbCache.setForceAlwaysDirty(forceAlwaysDirty);
            if (kbCacheTL != null) kbCacheTL.get().setForceAlwaysDirty(forceAlwaysDirty);
        } finally {
            writeLock.unlock();
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Stuff that is part of java.util.Map
    //
    // Recall that we're only implementing the parts that StringListStore needs
    ////////////////////////////////////////////////////////////////////////////

    @Override public void clear() {
        // Maybe some day becomes part of an "open, deleting pre-existing content"
        throw new RuntimeException("Not implemented");
    }

    @Override public boolean containsKey(Object key) {
        if (key instanceof String) {
            return get(key) != null;
        }
        return false;
    }

    @Override public boolean containsValue(Object value) {
        // lol no
        throw new RuntimeException("Not implemented");
    }

    @Override public Set<Map.Entry<String, RTWListValue>> entrySet() {
        // Screw that noise
        throw new RuntimeException("Not implemented");
    }

    // Skip implementation for equals and hashCode. We could define equality by the equality of the
    // Tokyo Cabinet file, but (in addition to it being subtle to do that correctly) two
    // TCHStoreMaps connected to the same file could show different views of the same data due to
    // caching.  So we'll keep it simple and say that there is no content-based meaning at all to
    // equality.

    @Override public RTWListValue get(Object key) {
        readLock.lock();
        try {
            Preconditions.checkState(db != null, "database is not open.");
            if (!(key instanceof String)) return null;
            String keyString = (String)key;

            RTWValue value;
            if (kbCache != null) value = kbCache.getValue(keyString);
            else value = kbCacheTL.get().getValue(keyString);
            if (value == null) return null;

            // This provides backward compatability to old KBs.  Autoconvert to a list.  No need to
            // mess with subslots on the value or anything.
            if (!(value instanceof RTWListValue)) { 
                value = new RTWArrayListValue(value); 
                if (!readOnly) {
                    if (kbCache != null) kbCache.putValue(keyString, (RTWListValue)value); 
                    else kbCacheTL.get().putValue(keyString, (RTWListValue)value);
                }
            } 
            return (RTWListValue)value;
        } finally {
            readLock.unlock();
        }
    }

    @Override public boolean isEmpty() {
        // Note that size() is potentially slow at present.
        return size() == 0;
    }
    
    @Override public Set<String> keySet() {
        return new KeySet();
    }

    @Override public RTWListValue put(String key, RTWListValue value) {
        writeLock.lock();
        try {
            Preconditions.checkState(db != null, "database is not open.");
            Preconditions.checkState(!isReadOnly(), "database is open read-only");
            RTWValue prev;
            if (kbCache != null) prev = kbCache.putValue(key, value);
            else throw new RuntimeException("Internal error: shouldn't have threadlocals in read-write mode");
            if (!(prev instanceof RTWListValue))
                return new RTWArrayListValue(prev); 
            return (RTWListValue)prev;
        } finally {
            writeLock.unlock();
        }
    }

    @Override public void putAll(Map<? extends String,? extends RTWListValue> m) {
        writeLock.lock();
        try {
            for (String key : m.keySet())
                put(key, m.get(key));
        } finally {
            writeLock.unlock();
        }
    }

    @Override public RTWListValue remove(Object key) {
        writeLock.lock();
        try {
            Preconditions.checkState(db != null, "database is not open.");
            Preconditions.checkState(!isReadOnly(), "database is open read-only");
            if (!(key instanceof String)) return null;
            String keyString = (String)key;
            RTWValue prev;
            if (kbCache != null) prev = kbCache.removeValue(keyString);
            else prev = kbCacheTL.get().removeValue(keyString);
            if (!(prev instanceof RTWListValue))
                return new RTWArrayListValue(prev); 
            return (RTWListValue)prev;
        } finally {
            writeLock.unlock();
        }
    }

    @Override public int size() {
        readLock.lock();
        try {
            Preconditions.checkState(db != null, "database is not open.");
        
            // This isn't very efficient.  If it becomes important, we can have kbCache keep track of
            // some delta to apply to the size reported by Tokyo Cabinet.
            if (kbCache != null) kbCache.commitAllDirty(true);
            else kbCacheTL.get().commitAllDirty(true);
            long l = db.rnum();
            if (l > Integer.MAX_VALUE)
                throw new RuntimeException("There are " + l
                        + " records, but Integer.MAX_VALUE is only " + Integer.MAX_VALUE);
            return (int)l;
        } finally {
            readLock.unlock();
        }
    }

    @Override public Collection<RTWListValue> values() {
        // Yeah, no.
        throw new RuntimeException("Not implemented.");
    }

    /**
     * Testing fixture
     */
    public static void main(String[] args) {
        TCHStoreMap storeMap = new TCHStoreMap();
        storeMap.open(args[0], true);

        // bkdb TODO: might as well make this a tool in tch temporarily
        MapDBStoreMap dstMap = new MapDBStoreMap();
        dstMap.open(args[1], false);
        for (String key : storeMap.keySet()) {
            dstMap.put(key, storeMap.get(key));
        }
        dstMap.close();
        storeMap.close();
        if (true) return;

        // bkdb: testing missing abstractthign memberofsets
        RTWListValue lv = storeMap.get("abstractthing memberofsets");
        System.out.println(lv.toString());
        if (true) return;

        for (String key : storeMap.keySet()) {
            System.out.println(key);
        }
    }
}
