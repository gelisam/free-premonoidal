{-# LANGUAGE AllowAmbiguousTypes, DataKinds, PolyKinds, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators #-}
module TypeLevel.List where

import Data.Constraint (Dict, withDict)
import Data.Proxy
import TypeLevel.Append
import TypeLevel.Axiom


nilP :: Proxy '[]
nilP = Proxy

appendP :: Proxy xs -> Proxy ys -> Proxy (xs ++ ys)
appendP Proxy Proxy = Proxy

withAssoc :: forall xs ys zs r
           . ( ((xs ++ ys) ++ zs)
             ~ (xs ++ (ys ++ zs))
            => r
             )
          -> r
withAssoc r
  = withDict (axiom :: Dict ( ((xs ++ ys) ++ zs)
                            ~ (xs ++ (ys ++ zs))
                            ))
             r
