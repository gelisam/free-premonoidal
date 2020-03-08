{-# LANGUAGE DataKinds, GADTs, KindSignatures, LambdaCase, RankNTypes, TypeOperators #-}
module List where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)
import TypeLevel.Append

import Consume
import KnownLength
import Premonoidal
import Tuple


data ToList (a :: Type)
            (as :: [Type])
            where
  Unit :: ToList () '[]
  Atom :: ToList a (a ': '[])
  Pair :: ToList a as
       -> ToList b bs
       -> ToList (a, b) (as ++ bs)

type FromList (as :: [Type])
              (a :: Type)
  = ToList a as

data FromSet (as :: [Type])
             (a :: Type)
             where
  FromSet :: ConsumeN as xs '[]
          -> FromList xs a
          -> FromSet as a

data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: ConsumeN as xs _bs
               -> FromList xs a
               -> FromSuperset as a


data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

runToListAndLengh
  :: Premonoidal r
  => ToList a as
  -> ( r a (Tuple as)
     , Length as
     )
runToListAndLengh = go1
  where
    go1
      :: Premonoidal r
      => ToList a as
      -> ( r a (Tuple as)
         , Length as
         )
    go1 = \case
      Unit -> let r = -- ()
                      id
                      -- []
              in (r, LNil)
      Atom -> let r = -- a
                      introR
                      -- (a, [])
              in (r, LCons LNil)
      Pair toListL toListR -> go2 toListL toListR

    go2
      :: Premonoidal r
      => ToList a as
      -> ToList b bs
      -> ( r (a, b)
             (Tuple (as ++ bs))
         , Length (as ++ bs)
         )
    go2 toListL toListR
      = let (rL, lenL) = go1 toListL
            (rR, lenR) = go1 toListR
            r          = -- (a, b)
                         first rL
                         -- (as, b)
                     >>> second rR
                         -- (as, bs)
                     >>> tappend lenL lenR
                         -- as ++ bs
        in (r, lappend lenL lenR)

runToList
  :: Premonoidal r
  => ToList a as
  -> r a (Tuple as)
runToList = fst . runToListAndLengh

runFromList
  :: Premonoidal r
  => FromList as a
  -> r (Tuple as) a
runFromList = fst . go1
  where
    go1
      :: Premonoidal r
      => FromList as a
      -> ( r (Tuple as) a
         , Length as
         )
    go1 = \case
      Unit -> let r = -- []
                      id
                      -- ()
              in (r, LNil)
      Atom -> let r = -- (a, [])
                      elimR
                      -- a
              in (r, LCons LNil)
      Pair fromListL fromListR -> go2 fromListL fromListR

    go2
      :: Premonoidal r
      => FromList as a
      -> FromList bs b
      -> ( r (Tuple (as ++ bs))
             (a, b)
         , Length (as ++ bs)
         )
    go2 fromListL fromListR
      = let (rL, lenL) = go1 fromListL
            (rR, lenR) = go1 fromListR
            r          = -- as ++ bs
                         tsplit lenL lenR
                         -- (as, bs)
                     >>> first rL
                         -- (a, bs)
                     >>> second rR
                         -- (a, b)
        in (r, lappend lenL lenR)

runFromSet
  :: Symmetric r
  => FromSet as a
  -> r (Tuple as) a
runFromSet (FromSet cN fromList)
    = -- as
      runConsumeN cN
      -- (xs, [])
  >>> elimR
      -- xs
  >>> runFromList fromList
      -- a

runFromSuperset
  :: Semicartesian r
  => FromSuperset as a
  -> r (Tuple as) a
runFromSuperset (FromSuperset cN fromList)
    = -- as
      runConsumeN cN
      -- (xs, bs)
  >>> second forget
      -- (xs, ()
  >>> elimR
      -- xs
  >>> runFromList fromList
      -- a


runListAction
  :: Premonoidal r
  => (forall x y. k x y -> r x y)
  -> ListAction k as bs
  -> ( r (Tuple as) (Tuple bs)
     , Length bs
     )
runListAction runK (ListAction fromList k toList)
  = let (rBs, lenBs) = runToListAndLengh toList
        r            = -- as
                       runFromList fromList
                       -- a
                   >>> runK k
                       -- b
                   >>> rBs
                       -- bs
    in (r, lenBs)


