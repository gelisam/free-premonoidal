{-# LANGUAGE DataKinds, GADTs, KindSignatures, LambdaCase, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Consume where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import KnownLength
import Premonoidal
import Tuple


data Consume1 (as :: [Type])  -- all elements
              (x :: Type)     -- consumed element
              (bs :: [Type])  -- remaining elements
              where
  CHere  :: Consume1 (x ': as) x as
  CThere :: Consume1 as x bs
         -> Consume1 (y ': as) x (y ': bs)

data ConsumeN (as :: [Type])  -- all elements
              (xs :: [Type])  -- consumed elements
              (bs :: [Type])  -- remaining elements
              where
  CNil  :: ConsumeN as '[] as
  CCons :: Consume1 as x bs
        -> ConsumeN bs xs cs
        -> ConsumeN as (x ': xs) cs

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
  => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                    , Length ys
                                    ))
  -> Consuming action as bs
  -> TArrow r as bs
runConsuming runAction (Consuming cN action)
  = TArrow $ go runAction cN action
  where
    go
      :: forall r action as xs ys rest. Symmetric r
      => (forall xs ys. action xs ys -> ( r (Tuple xs) (Tuple ys)
                                        , Length ys
                                        ))
      -> ConsumeN as xs rest
      -> action xs ys
      -> r (Tuple as)
           (Tuple (ys ++ rest))
    go runAction cN action
      = let (rA, lenYs) = runAction action
            r           = -- as
                          runConsumeN cN
                          -- (xs, rest)
                      >>> first rA
                          -- (ys, rest)
                      >>> tappend lenYs (Proxy @rest)
                          -- ys ++ rest
        in r
