{-# LANGUAGE DataKinds, GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Observe where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import KnownLength
import Premonoidal
import Tuple


-- e.g. Observe1 [a, b, x, c] x
data Observe1 (as :: [Type])  -- all elements
              (x :: Type)     -- observed element
              where
  OHere  :: Observe1 (x ': as) x
  OThere :: Observe1 as x
         -> Observe1 (y ': as) x

-- e.g. ObserveN [a, b, x1, c, x2] [x1, x2]
data ObserveN (as :: [Type])  -- all elements
              (xs :: [Type])  -- observed elements
              where
  ONil  :: ObserveN as '[]
  OCons :: Observe1 as x
        -> ObserveN as xs
        -> ObserveN as (x ': xs)

-- e.g.
-- action :: r [x1, x2] [y1, y2, y3]
-- Observing _ action :: Observing r [a, b, x1, c, x2]
--                                   [y1, y2, y3, a, b, x1, c, x2]
data Observing (action :: [Type] -> [Type] -> Type)
               (as :: [Type])  -- original elements
               (bs :: [Type])  -- produced ++ original elements
               where
  Observing :: ObserveN as xs
            -> action xs ys
            -> Observing action as (ys ++ as)

runObserve1
  :: Semicartesian r
  => Observe1 as x
  -> r (Tuple as) x
runObserve1 = \case
  OHere -> -- (x, as)
           second forget
           -- (x, ())
       >>> elimR
           -- x
  OThere o1 -> -- (y, as)
               second (runObserve1 o1)
               -- (y, x)
           >>> first forget
               -- ((), x)
           >>> elimL

runObserveN
  :: Cartesian r
  => ObserveN as xs
  -> r (Tuple as) (Tuple xs)
runObserveN = \case
  ONil -> -- as
          forget
          -- []
  OCons o1 oN -> -- as
                 dup
                 -- (as, as)
             >>> first (runObserve1 o1)
                 -- (x, as)
             >>> second (runObserveN oN)
                 -- (x, xs)

runObserving
  :: Cartesian r
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Observing action as bs
  -> TArrow r as bs
runObserving runAction (Observing oN action)
  = TArrow $ go runAction oN action
  where
    go
      :: forall r action as xs ys. Cartesian r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> ObserveN as xs
      -> action xs ys
      -> r (Tuple as)
           (Tuple (ys ++ as))
    go runAction oN action
      = let (rA, lenYs) = runAction action
            r           = -- as
                          dup
                          -- (as, as)
                      >>> first (runObserveN oN)
                          -- (xs, as)
                      >>> first rA
                          -- (ys, as)
                      >>> tappend lenYs (Proxy @as)
                          -- ys ++ as
        in r

observeAll
  :: Length as
  -> ObserveN as as
observeAll LNil
  = ONil
observeAll (LCons len)
  = OCons OHere
          (shift (observeAll len))
  where
    shift
      :: ObserveN as xs
      -> ObserveN (a ': as) xs
    shift ONil = ONil
    shift (OCons o1 oN) = OCons (OThere o1)
                                (shift oN)

singletonObserve1
  :: Observe1 '[a] a
singletonObserve1
  = OHere

singletonObserveN
  :: ObserveN '[a] '[a]
singletonObserveN
  = observeAll one

singletonObserving
  :: Length as
  -> action as bs
  -> Observing action as (bs ++ as)
singletonObserving len action
  = Observing (observeAll len) action
