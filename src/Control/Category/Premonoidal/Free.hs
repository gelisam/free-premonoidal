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


data Atom
       (q :: [k] -> [k] -> Type)
       (as :: [k])
       (bs :: [k])
       where
  Atom
    :: Proxy xs
    -> q as bs
    -> Proxy zs
    -> Atom q (xs ++ as ++ zs)
              (xs ++ bs ++ zs)

type Free q = FreeCategory (Atom q)


instance Premonoidal (Atom q) where
  widen ws (Atom xs q ys) zs
    = go ws xs q ys zs
    where
      go :: forall q ws xs as bs ys zs
          . Proxy ws
         -> Proxy xs
         -> q as bs
         -> Proxy ys
         -> Proxy zs
         -> Atom q (ws ++ (xs ++ as ++ ys) ++ zs)
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
        $ Atom (appendP ws xs) q (appendP ys zs)

instance Premonoidal (Free q) where
  widen _ Id _
    = Id
  widen xs (q :>>> qs) zs
        = widen xs q zs
     :>>> widen xs qs zs


runAtom
  :: Premonoidal r
  => (forall xs ys. q xs ys -> r xs ys)
  -> Atom q as bs -> r as bs
runAtom runQ (Atom xs q ys)
  = widen xs (runQ q) ys

runFree
  :: (Category r, Premonoidal r)
  => (forall xs ys. q xs ys -> r xs ys)
  -> Free q as bs -> r as bs
runFree runQ
  = runFreeCategory (runAtom runQ)
