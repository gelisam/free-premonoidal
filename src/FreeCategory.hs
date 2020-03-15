{-# LANGUAGE GADTs, LambdaCase, PolyKinds, RankNTypes #-}
module FreeCategory where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)


data FreeCategory (k :: i -> i -> Type)
                  (a :: i)
                  (b :: i)
                  where
  Id     :: FreeCategory k a a
  (:>>>) :: k a b
         -> FreeCategory k b c
         -> FreeCategory k a c

instance Category (FreeCategory k) where
  id = Id
  (.) = flip go where
    go :: FreeCategory k a b
       -> FreeCategory k b c
       -> FreeCategory k a c
    go Id           gs = gs
    go (f :>>> fs) gs = f :>>> go fs gs

runFreeCategory
  :: Category r
  => (forall x y. k x y -> r x y)
  -> FreeCategory k a b -> r a b
runFreeCategory runK = \case
  Id        -> id
  f :>>> fs -> runK f
           >>> runFreeCategory runK fs

mapFreeCategory
  :: (forall x y. k x y -> r x y)
  -> FreeCategory k a b
  -> FreeCategory r a b
mapFreeCategory f = \case
  Id -> Id
  k :>>> ks -> f k :>>> mapFreeCategory f ks

singletonFreeCategory
  :: k a b
  -> FreeCategory k a b
singletonFreeCategory k = k :>>> Id
