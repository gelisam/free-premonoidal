{-# LANGUAGE DataKinds, GADTs, KindSignatures, FlexibleInstances, InstanceSigs, PolyKinds, RankNTypes, ScopedTypeVariables, TypeOperators, TypeSynonymInstances #-}
module FreePremonoidal where

import Control.Category
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

firstAtom
  :: PremonoidalAtom q as bs
  -> Proxy zs
  -> PremonoidalAtom q (as ++ zs) (bs ++ zs)
firstAtom (PremonoidalAtom xs q ys) zs
  = undefined
  -- = PremonoidalAtom xs q (appendP ys zs)

secondAtom
  :: Proxy xs
  -> PremonoidalAtom q as bs
  -> PremonoidalAtom q (xs ++ as) (xs ++ bs)
secondAtom xs (PremonoidalAtom ys q zs)
  = undefined
  -- = PremonoidalAtom (appendP xs ys) q zs

type FreePremonoidal q = FreeCategory (PremonoidalAtom q)

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


--runFreePremonoidal
--  :: forall r q a b. Premonoidal r
--  => (forall x y. q x y -> r x y)
--  -> FreePremonoidal q a b -> r a b
--runFreePremonoidal runK (FreePremonoidal toList
--                                         dividingActions
--                                         fromList)
--    = -- a
--      runToList toList
--      -- as
--  >>> runTArrow (runFreeCategory runAction dividingActions)
--      -- bs
--  >>> runFromList fromList
--      -- b
--  where
--    runAction
--      :: Dividing (ListAction q) xs ys
--      -> TArrow r xs ys
--    runAction = runDividing (runListAction runK) listActionOutputLength
