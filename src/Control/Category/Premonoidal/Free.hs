{-# LANGUAGE DataKinds, GADTs, KindSignatures, FlexibleInstances, InstanceSigs, PolyKinds, RankNTypes, ScopedTypeVariables, TypeApplications, TypeOperators, TypeSynonymInstances #-}
{-# OPTIONS -Wno-name-shadowing #-}
module Control.Category.Premonoidal.Free where

import Control.Category
import Data.Kind (Type)
import Data.Proxy
import TypeLevel.Append

import Control.Category.Free
import Control.Category.Premonoidal
import TypeLevel.List


data PremonoidalAtom
       (q :: [k] -> [k] -> Type)
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


instance Premonoidal (PremonoidalAtom q) where
  widen ws (PremonoidalAtom xs q ys) zs
    = go ws xs q ys zs
    where
      go :: forall q ws xs as bs ys zs
          . Proxy ws
         -> Proxy xs
         -> q as bs
         -> Proxy ys
         -> Proxy zs
         -> PremonoidalAtom q (ws ++ (xs ++ as ++ ys) ++ zs)
                              (ws ++ (xs ++ bs ++ ys) ++ zs)
      go ws xs q ys zs
       -- (ws ++ ((xs ++ _) ++ ys)) ++ zs
        = withAssoc @ws @(xs ++ as) @ys
        $ withAssoc @ws @(xs ++ bs) @ys
       -- ((ws ++ (xs ++ _)) ++ ys) ++ zs
        $ withAssoc @ws @xs @as
        $ withAssoc @ws @xs @bs
       -- (((ws ++ xs) ++ _) ++ ys) ++ zs
        $ withAssoc @(ws ++ xs ++ as) @ys @zs
        $ withAssoc @(ws ++ xs ++ bs) @ys @zs
       -- ((ws ++ xs) ++ _) ++ (ys ++ zs)
        $ PremonoidalAtom (appendP ws xs) q (appendP ys zs)

instance Premonoidal (FreePremonoidal q) where
  widen _ Id _
    = Id
  widen xs (q :>>> qs) zs
        = widen xs q zs
     :>>> widen xs qs zs


runPremonoidalAtom
  :: Premonoidal r
  => (forall xs ys. q xs ys -> r xs ys)
  -> PremonoidalAtom q as bs -> r as bs
runPremonoidalAtom runQ (PremonoidalAtom xs q ys)
  = widen xs (runQ q) ys

runFreePremonoidal
  :: (Category r, Premonoidal r)
  => (forall xs ys. q xs ys -> r xs ys)
  -> FreePremonoidal q as bs -> r as bs
runFreePremonoidal runQ
  = runFreeCategory (runPremonoidalAtom runQ)
