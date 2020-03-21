{-# LANGUAGE DataKinds, GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fplugin TypeLevel.Rewrite
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightIdentity
                -fplugin-opt=TypeLevel.Rewrite:TypeLevel.Append.RightAssociative #-}
module Consume where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import KnownLength
import Premonoidal
import Tuple


-- e.g. Consume1 [a, b, x, c] x [a, b, c]
data Consume1 (as :: [Type])  -- all elements
              (x :: Type)     -- consumed element
              (bs :: [Type])  -- remaining elements
              where
  CHere  :: Consume1 (x ': as) x as
  CThere :: Consume1 as x bs
         -> Consume1 (y ': as) x (y ': bs)

-- e.g. Consume1 [a, b, x1, c, x2] [x1, x2] [a, b, c]
data ConsumeN (as :: [Type])  -- all elements
              (xs :: [Type])  -- consumed elements
              (bs :: [Type])  -- remaining elements
              where
  CNil  :: ConsumeN as '[] as
  CCons :: Consume1 as x bs
        -> ConsumeN bs xs cs
        -> ConsumeN as (x ': xs) cs

-- e.g.
-- action :: r [x1, x2] [y1, y2, y3]
-- Consuming _ action :: Consuming r [a, b, x1, c, x2]
--                                   [y1, y2, y3, a, b, c]
data Consuming (action :: [Type] -> [Type] -> Type)
               (as :: [Type])  -- all elements
               (bs :: [Type])  -- produced ++ remaining elements
               where
  Consuming :: ConsumeN as xs rest
            -> action xs ys
            -> Consuming action as (ys ++ rest)

runConsume1
  :: Symmetric r
  => Consume1 as x bs
  -> r (Tuple as)
       (x, Tuple bs)
runConsume1 = \case
  CHere -> -- (x, as)
           id
           -- (x, as)
  CThere c1 -> -- (y, as)
               second (runConsume1 c1)
               -- (y, (x, bs))
           >>> assocL
               -- ((y, x), bs)
           >>> first swap
               -- ((x, y), bs)
           >>> assocR
               -- (x, (y, bs))

runConsumeN
  :: Symmetric r
  => ConsumeN as xs bs
  -> r (Tuple as)
       (Tuple xs, Tuple bs)
runConsumeN = \case
  CNil -> -- as
          introL
          -- ([], as)
  CCons c1 cN -> -- as
                 runConsume1 c1
                 -- (x, bs)
             >>> second (runConsumeN cN)
                 -- (x, (xs, cs))
             >>> assocL
                 -- ((x, xs), cs)

runConsuming
  :: Symmetric r
  => (forall xs ys. action xs ys -> r (Tuple xs) (Tuple ys))
  -> (forall xs ys. action xs ys -> Length ys)
  -> Consuming action as bs
  -> TArrow r as bs
runConsuming runAction outputLength (Consuming cN action)
  = TArrow $ go runAction outputLength cN action
  where
    go
      :: forall r action as xs ys rest. Symmetric r
      => (forall xs ys. action xs ys -> r (Tuple xs) (Tuple ys))
      -> (forall xs ys. action xs ys -> Length ys)
      -> ConsumeN as xs rest
      -> action xs ys
      -> r (Tuple as)
           (Tuple (ys ++ rest))
    go runAction outputLength cN action
        = -- as
          runConsumeN cN
          -- (xs, rest)
      >>> first (runAction action)
          -- (ys, rest)
      >>> tappend (outputLength action)
                  (Proxy @rest)
          -- ys ++ rest

consumeAll
  :: Length as
  -> ConsumeN as as '[]
consumeAll LNil = CNil
consumeAll (LCons len) = CCons CHere (consumeAll len)

singletonConsume1
  :: Consume1 '[a] a '[]
singletonConsume1
  = CHere

singletonConsumeN
  :: ConsumeN '[a] '[a] '[]
singletonConsumeN
  = consumeAll one

singletonConsuming
  :: Length as
  -> action as bs
  -> Consuming action as bs
singletonConsuming len action
  = Consuming (consumeAll len) action
