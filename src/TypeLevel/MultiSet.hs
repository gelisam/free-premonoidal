{-# LANGUAGE AllowAmbiguousTypes, DataKinds, PolyKinds, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators #-}
module TypeLevel.MultiSet where

import Data.Constraint (Dict, withDict)
import Data.Proxy
import TypeLevel.Append

import TypeLevel.Axiom


type family MultiSet (as :: [k])

nilP :: Proxy (MultiSet '[])
nilP = Proxy

appendP
  :: Proxy (MultiSet xs)
  -> Proxy (MultiSet ys)
  -> Proxy (MultiSet (xs ++ ys))
appendP Proxy Proxy = Proxy

withCommut
  :: forall xs ys r
   . ( MultiSet (xs ++ ys)
     ~ MultiSet (ys ++ xs)
    => r
     )
  -> r
withCommut r
  = withDict (axiom :: Dict ( MultiSet (xs ++ ys)
                            ~ MultiSet (ys ++ xs)
                            ))
             r

withAssoc
  :: forall xs ys zs r
   . ( MultiSet ((xs ++ ys) ++ zs)
     ~ MultiSet (xs ++ (ys ++ zs))
    => r
     )
  -> r
withAssoc r
  = withDict (axiom :: Dict ( MultiSet ((xs ++ ys) ++ zs)
                            ~ MultiSet (xs ++ (ys ++ zs))
                            ))
             r
