module WriteOnce (WORef, create, set, get) where

import Data.IORef

newtype WORef a = WORef (IORef (Maybe a))

create :: IO (WORef a)
create = do
  r <- newIORef Nothing
  return $ WORef r

set :: WORef a -> a -> IO ()
set (WORef r) x = do
  v <- readIORef r
  case v of
   Nothing -> writeIORef r (Just x)
   Just _ -> error "set: double write!"

get :: WORef a -> IO a
get (WORef r) = do
  v <- readIORef r
  case v of
   Nothing -> error "get: read before write!"
   Just x -> return x
       
