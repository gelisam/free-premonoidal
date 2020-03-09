{-# LANGUAGE GADTs, KindSignatures, RankNTypes, ScopedTypeVariables #-}
module FreePremonoidal where

import Control.Category
import Data.Kind (Type)

import Consume
import Divide
import FreeCategory
import List
import Observe
import Premonoidal
import Tuple


data FreePremonoidal (k :: Type -> Type -> Type)
                     (a :: Type)
                     (b :: Type)
                     where
  FreePremonoidal
    :: ToList a as
    -> FreeCategory (Dividing (ListAction k)) as bs
    -> FromList bs b
    -> FreePremonoidal k a b

data FreeSymmetric (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeSymmetric
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSet bs b
    -> FreeSymmetric k a b

data FreeSemicartesian (k :: Type -> Type -> Type)
                       (a :: Type)
                       (b :: Type)
                       where
  FreeSemicartesian
    :: ToList a as
    -> FreeCategory (Consuming (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeSemicartesian k a b

data FreeCartesian (k :: Type -> Type -> Type)
                   (a :: Type)
                   (b :: Type)
                   where
  FreeCartesian
    :: ToList a as
    -> FreeCategory (Observing (ListAction k)) as bs
    -> FromSuperset bs b
    -> FreeCartesian k a b


runFreePremonoidal
  :: forall r k a b. Premonoidal r
  => (forall x y. k x y -> r x y)
  -> FreePremonoidal k a b -> r a b
runFreePremonoidal runK (FreePremonoidal toList
                                         dividingActions
                                         fromList)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction dividingActions)
      -- bs
  >>> runFromList fromList
      -- b
  where
    runAction
      :: Dividing (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runDividing (runListAction runK)

runFreeSymmetric
  :: forall r k a b. Symmetric r
  => (forall x y. k x y -> r x y)
  -> FreeSymmetric k a b -> r a b
runFreeSymmetric runK (FreeSymmetric toList
                                     consumingActions
                                     fromSet)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction consumingActions)
      -- bs
  >>> runFromSet fromSet
      -- b
  where
    runAction
      :: Consuming (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runConsuming (runListAction runK)

runFreeSemicartesian
  :: forall r k a b. Semicartesian r
  => (forall x y. k x y -> r x y)
  -> FreeSemicartesian k a b -> r a b
runFreeSemicartesian runK (FreeSemicartesian toList
                                             consumingActions
                                             fromSuperset)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction consumingActions)
      -- bs
  >>> runFromSuperset fromSuperset
      -- b
  where
    runAction
      :: Consuming (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runConsuming (runListAction runK)

runFreeCartesian
  :: forall r k a b. Cartesian r
  => (forall x y. k x y -> r x y)
  -> FreeCartesian k a b -> r a b
runFreeCartesian runK (FreeCartesian toList
                                     observingActions
                                     fromSuperset)
    = -- a
      runToList toList
      -- as
  >>> runTArrow (runFreeCategory runAction observingActions)
  >>> runFromSuperset fromSuperset
  where
    runAction
      :: Observing (ListAction k) xs ys
      -> TArrow r xs ys
    runAction = runObserving (runListAction runK)
