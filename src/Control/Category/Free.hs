{-# LANGUAGE GADTs, LambdaCase, PolyKinds, RankNTypes #-}
module Control.Category.Free where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)


data FreeCategory
       (q :: k -> k -> Type)
       (a :: k)
       (b :: k)
       where
  Id     :: FreeCategory q a a
  (:>>>) :: q a b
         -> FreeCategory q b c
         -> FreeCategory q a c

instance Category (FreeCategory q) where
  id = Id
  (.) = flip go where
    go :: FreeCategory q a b
       -> FreeCategory q b c
       -> FreeCategory q a c
    go Id           gs = gs
    go (f :>>> fs) gs = f :>>> go fs gs

runFreeCategory
  :: Category r
  => (forall x y. q x y -> r x y)
  -> FreeCategory q a b -> r a b
runFreeCategory runK = \case
  Id        -> id
  f :>>> fs -> runK f
           >>> runFreeCategory runK fs

mapFreeCategory
  :: (forall x y. q x y -> r x y)
  -> FreeCategory q a b
  -> FreeCategory r a b
mapFreeCategory f = \case
  Id -> Id
  q :>>> ks -> f q :>>> mapFreeCategory f ks

singletonFreeCategory
  :: q a b
  -> FreeCategory q a b
singletonFreeCategory q = q :>>> Id
