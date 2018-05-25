{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE CPP, DeriveDataTypeable #-}
{-# LANGUAGE BangPatterns #-}

#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Concurrent.STM.RTTQueue2
-- Copyright   :  (c) The University of Glasgow 2012
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (requires STM)
--
-- A 'TQueue' is like a 'TChan', with two important differences:
--
--  * it has faster throughput than both 'TChan' and 'Chan'
--
--  * it does /not/ provide equivalents of the 'dupTChan' and
--    'cloneTChan' operations.
--
-- The implementation is based on Okasaki's scheduled banker's queues,
-- but it uses *two* schedules so there's only contention between the
-- reader and writer when the queue needs to be rotated.
--
-----------------------------------------------------------------------------

module Control.Concurrent.STM.RTTQueue2 (
        -- * TQueue
        TQueue,
        newTQueue,
        newTQueueIO,
        readTQueue,
        tryReadTQueue,
        flushTQueue,
        peekTQueue,
        tryPeekTQueue,
        writeTQueue,
        unGetTQueue,
        isEmptyTQueue,
  )  where

import GHC.Conc
import Control.Monad (unless)
import Data.Typeable (Typeable)

-- | 'TQueue' is an abstract type representing an unbounded FIFO channel.
--
-- @since 2.4
data TQueue a = TQueue {-# UNPACK #-} !(TVar [a]) -- Front list
                       {-# UNPACK #-} !(TVar [a]) -- Front schedule
                       {-# UNPACK #-} !(TVar [a]) -- Rear list
                       {-# UNPACK #-} !(TVar [a]) -- Rear schedule
  deriving Typeable
{-
Invariant:

Given front list, rear list, front schedule, and rear schedule called
front, rear, fsched, and rsched, respectively,

    2 * (|front| - |rear|) = |fsched| + |rsched|

Note that because lengths cannot be negative, this implies that

    |front| >= |rear|

We rotate the queue when either schedule is empty. This preserves
the invariant and ensures that the spine of the front list is
fully realized when a rotation occurs. The spine of the rear list
is *always* fully realized. We could use a strict-spined list for
the rear, but it doesn't really seem to be worth the trouble.
-}

instance Eq (TQueue a) where
  TQueue a _ _ _ == TQueue b _ _ _ = a == b

-- | Build and returns a new instance of 'TQueue'
newTQueue :: STM (TQueue a)
newTQueue = do
  read  <- newTVar []
  fschedule <- newTVar []
  write <- newTVar []
  rschedule <- newTVar []
  return (TQueue read fschedule write rschedule)

-- | @IO@ version of 'newTQueue'.  This is useful for creating top-level
-- 'TQueue's using 'System.IO.Unsafe.unsafePerformIO', because using
-- 'atomically' inside 'System.IO.Unsafe.unsafePerformIO' isn't
-- possible.
newTQueueIO :: IO (TQueue a)
newTQueueIO = do
  read  <- newTVarIO []
  fschedule <- newTVarIO []
  write <- newTVarIO []
  rschedule <- newTVarIO []
  return (TQueue read fschedule write rschedule)

-- rotate front end = front ++ reverse rear, but the reverse is performed
-- incrementally as the append proceeds.
--
-- Precondition: |front| + 1 >= |rear|. This ensures that when the front
-- list is empty, the rear list has at most one element, so we don't need
-- to reverse it.
rotate :: [a] -> [a] -> [a]
rotate = go []
  where
    go acc [] rear = rear ++ acc
    go acc (x:xs) (r:rs)
      = x : go (r:acc) xs rs
    go acc xs [] = xs ++ acc

-- | Write a value to a 'TQueue'.
writeTQueue :: TQueue a -> a -> STM ()
writeTQueue (TQueue read fschedule write rschedule) a = do
  listend <- readTVar write
  rsched <- readTVar rschedule
  let listend' = a : listend
  case rsched of
    -- Reduce |front|-|rear| by 1; reduce |fsched|+|rsched| by 2
    _:_:rsched' -> writeTVar write listend'
                   >> writeTVar rschedule rsched'

    -- Rotate the queue; the invariant holds trivially.
    _ -> do
      listfront <- readTVar read
      let !front' = rotate listfront listend'
      writeTVar read front'
      writeTVar fschedule front'
      writeTVar write []
      writeTVar rschedule front'

-- | Read the next value from the 'TQueue'.
readTQueue :: TQueue a -> STM a
readTQueue (TQueue read fschedule write rschedule) = do
  listfront <- readTVar read
  fsched <- readTVar fschedule
  case listfront of
    [] -> retry
    x:front' ->
      case fsched of
        -- Reduce |front|-|rear| by 1; reduce |fsched|+|rsched| by 2
        _:_:fsched' -> writeTVar read front'
                         >> writeTVar fschedule fsched' >> return x

        -- Rotate the queue; the invariant holds trivially.
        _ -> do
          listend <- readTVar write
          let !front'' = rotate front' listend
          writeTVar read front''
          writeTVar fschedule front''
          writeTVar write []
          writeTVar rschedule front''
          return x

-- | A version of 'readTQueue' which does not retry. Instead it
-- returns @Nothing@ if no value is available.
tryReadTQueue :: TQueue a -> STM (Maybe a)
tryReadTQueue c = fmap Just (readTQueue c) `orElse` return Nothing

-- | Efficiently read the entire contents of a 'TQueue' into a list. This
-- function never retries.
--
-- @since 2.4.5
flushTQueue :: TQueue a -> STM [a]
flushTQueue (TQueue read fschedule write rschedule) = do
  front <- readTVar read
  fsched <- readTVar fschedule
  rear <- readTVar write
  rsched <- readTVar rschedule
  unless (null front) $ writeTVar read []
  unless (null fsched) $ writeTVar fschedule []
  unless (null rear) $ writeTVar write []
  unless (null rsched) $ writeTVar rschedule []
  return (rotate front rear)

-- | Get the next value from the @TQueue@ without removing it,
-- retrying if the channel is empty.
peekTQueue :: TQueue a -> STM a
peekTQueue (TQueue read _fschedule _write _rschedule) = do
  front <- readTVar read
  case front of
    x:_ -> return x
    [] -> retry

-- | A version of 'peekTQueue' which does not retry. Instead it
-- returns @Nothing@ if no value is available.
tryPeekTQueue :: TQueue a -> STM (Maybe a)
tryPeekTQueue (TQueue read _fschedule _write _rschedule) = do
  front <- readTVar read
  case front of
    x:_ -> return (Just x)
    [] -> return Nothing

-- | Put a data item back onto a channel, where it will be the next item read.
unGetTQueue :: TQueue a -> a -> STM ()
unGetTQueue (TQueue read fschedule _write _rschedule) a = do
  front <- readTVar read
  fsched <- readTVar fschedule
  writeTVar read (a:front)
  writeTVar fschedule (a:a:fsched)

-- | Returns 'True' if the supplied 'TQueue' is empty.
isEmptyTQueue :: TQueue a -> STM Bool
isEmptyTQueue (TQueue read _fschedule _write _rschedule) = do
  front <- readTVar read
  return $! null front
