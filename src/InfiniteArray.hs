{-- This module implements infinite arrays, that is, arrays that grow
    transparently upon demand. -}

module InfiniteArray where

import Data.Array.MArray
import Data.Array.IO
import Data.IORef

import Control.Monad

data InfiniteArray a = InfiniteArray {
  def   :: a,
  table :: IORef (IOArray Int a)
}

make default_size x = do
  t <- newArray (0, default_size) x
  r <- newIORef t
  return $ InfiniteArray x r

new_length length i =
  if i < length
  then length
  else new_length (2 * length) i

ensure :: InfiniteArray a -> Int -> IO ()       
ensure a i = do
  t <- readIORef (table a)
  (_,length) <- getBounds t
  when (i >= length) $ do
    t' <- newArray (0, new_length (2 * length) i) (def a)
    forM_ [0 .. (length-1)] (\ i -> do
        x <- readArray t i
        writeArray t' i x)
    writeIORef (table a) t'

get a i = do
  ensure a i
  t <- readIORef (table a)
  readArray t i

set a i x = do
  ensure a i
  t <- readIORef (table a)
  writeArray t i x
      
  

