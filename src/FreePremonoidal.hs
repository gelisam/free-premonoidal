{-# LANGUAGE DataKinds, GADTs, KindSignatures, FlexibleInstances, InstanceSigs, PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators, TypeSynonymInstances #-}
{-# OPTIONS -Wno-name-shadowing #-}
module FreePremonoidal where

import Data.Kind (Type)
import Data.Proxy

import FreeCategory
import Premonoidal
import TypeLevel.Append
import TypeLevel.List


data PremonoidalAtom (q :: [k] -> [k] -> Type)
                     (as :: [k])
                     (bs :: [k])
                     where
  PremonoidalAtom
    :: Proxy xs
    -> q as bs
    -> Proxy zs
    -> PremonoidalAtom q (xs ++ as ++ zs)
                         (xs ++ bs ++ zs)

type FreePremonoidal q = FreeCategory (PremonoidalAtom q)


firstAtom
  :: PremonoidalAtom q as bs
  -> Proxy zs
  -> PremonoidalAtom q (as ++ zs)
                       (bs ++ zs)
firstAtom (PremonoidalAtom xs q ys) zs
  = go xs q ys zs
  where
    go :: forall q xs as bs ys zs
        . Proxy xs
       -> q as bs
       -> Proxy ys
       -> Proxy zs
       -> PremonoidalAtom q ((xs ++ as ++ ys) ++ zs)
                            ((xs ++ bs ++ ys) ++ zs)
    go xs q ys zs
     -- ((xs ++ _) ++ ys) ++ zs
      = withAssoc @(xs ++ as) @ys @zs
      $ withAssoc @(xs ++ bs) @ys @zs
     -- (xs ++ _) ++ (ys ++ zs)
      $ PremonoidalAtom xs q (appendP ys zs)

secondAtom
  :: Proxy xs
  -> PremonoidalAtom q as bs
  -> PremonoidalAtom q (xs ++ as) (xs ++ bs)
secondAtom xs (PremonoidalAtom ys q zs)
  = go xs ys q zs
  where
    go :: forall q xs ys as bs zs
        . Proxy xs
       -> Proxy ys
       -> q as bs
       -> Proxy zs
       -> PremonoidalAtom q (xs ++ (ys ++ as ++ zs))
                            (xs ++ (ys ++ bs ++ zs))
    go xs ys q zs
     -- xs ++ ((ys ++ as) ++ zs)
      = withAssoc @xs @ys @as
      $ withAssoc @xs @ys @bs
     -- (xs ++ (ys ++ as)) ++ zs
      $ withAssoc @xs @(ys ++ as) @zs
      $ withAssoc @xs @(ys ++ bs) @zs
     -- ((xs ++ ys) ++ as) ++ zs
      $ PremonoidalAtom (appendP xs ys) q zs

instance Premonoidal (FreePremonoidal q) where
  first Id _
    = Id
  first (q :>>> qs) zs
        = firstAtom q zs
     :>>> first qs zs
  second _ Id
    = Id
  second xs (q :>>> qs)
        = secondAtom xs q
     :>>> second xs qs


runPremonoidalAtom
  :: Premonoidal r
  => (forall xs ys. q xs ys -> r xs ys)
  -> PremonoidalAtom q as bs -> r as bs
runPremonoidalAtom runQ (PremonoidalAtom xs q ys)
  = first (second xs (runQ q)) ys

runFreePremonoidal
  :: Premonoidal r
  => (forall xs ys. q xs ys -> r xs ys)
  -> FreePremonoidal q as bs -> r as bs
runFreePremonoidal runQ
  = runFreeCategory (runPremonoidalAtom runQ)
