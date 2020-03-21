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


-- e.g.
-- ToList ((a, ()), ((), b)) [(a, ()), ((), b)]
-- ToList ((a, ()), ((), b)) [a, (), (), b]
-- ToList ((a, ()), ((), b)) [a, b]
data ToList (a :: Type)
            (as :: [Type])
            where
  Unit :: ToList () '[]
  Atom :: ToList a (a ': '[])
  Pair :: ToList a as
       -> ToList b bs
       -> ToList (a, b) (as ++ bs)

-- e.g. FromList [a, b, c, d] ((a, b), (c, d))
type FromList (as :: [Type])
              (a :: Type)
  = ToList a as

-- e.g. FromSet [b, c, a, d] ((a, b), (c, d))
data FromSet (as :: [Type])
             (a :: Type)
             where
  FromSet :: ConsumeN as xs '[]
          -> FromList xs a
          -> FromSet as a

-- e.g. FromSet [x, b, c, y, a, d, z] ((a, b), (c, d))
data FromSuperset (as :: [Type])
                  (a :: Type)
                  where
  FromSuperset :: ConsumeN as xs _bs
               -> FromList xs a
               -> FromSuperset as a

-- e.g.
-- f :: k (x1, x2) (y1, (y2, y3))
-- ListAction _ _ action :: ListAction k [x1, x2]
--                                       [y1, y2 y3]
data ListAction (k :: Type -> Type -> Type)
                (as :: [Type])
                (bs :: [Type])
                where
  ListAction :: FromList as a
             -> k a b
             -> ToList b bs
             -> ListAction k as bs

toListLength
  :: ToList a as
  -> Length as
toListLength = \case
  Unit -> LNil
  Atom -> one
  Pair l r -> toListLength l
    `lappend` toListLength r

fromListLength
  :: FromList as a
  -> Length as
fromListLength = toListLength

runToList
  :: Premonoidal r
  => ToList a as
  -> r a (Tuple as)
runToList = go1
  where
    go1
      :: Premonoidal r
      => ToList a as
      -> r a (Tuple as)
    go1 = \case
      Unit -> -- ()
              id
              -- []
      Atom -> -- a
              introR
              -- (a, [])
      Pair toListL toListR -> go2 toListL toListR

    go2
      :: Premonoidal r
      => ToList a as
      -> ToList b bs
      -> r (a, b)
           (Tuple (as ++ bs))
    go2 toListL toListR
        = -- (a, b)
          first (go1 toListL)
          -- (as, b)
      >>> second (go1 toListR)
          -- (as, bs)
      >>> tappend (toListLength toListL)
                  (toListLength toListR)
          -- as ++ bs

runFromList
  :: Premonoidal r
  => FromList as a
  -> r (Tuple as) a
runFromList = go1
  where
    go1
      :: Premonoidal r
      => FromList as a
      -> r (Tuple as) a
    go1 = \case
      Unit -> -- []
              id
              -- ()
      Atom -> -- (a, [])
              elimR
              -- a
      Pair fromListL fromListR -> go2 fromListL fromListR

    go2
      :: Premonoidal r
      => FromList as a
      -> FromList bs b
      -> r (Tuple (as ++ bs))
           (a, b)
    go2 fromListL fromListR
        = -- as ++ bs
          tsplit (fromListLength fromListL)
                 (fromListLength fromListR)
          -- (as, bs)
      >>> first (go1 fromListL)
          -- (a, bs)
      >>> second (go1 fromListR)
          -- (a, b)
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
  -> r (Tuple as) (Tuple bs)
runListAction runK (ListAction fromList k toList)
    = -- as
      runFromList fromList
      -- a
  >>> runK k
      -- b
  >>> runToList toList
      -- bs

listActionOutputLength
  :: ListAction k as bs
  -> Length bs
listActionOutputLength (ListAction _ _ toList)
  = toListLength toList

singletonToList
  :: ToList a '[a]
singletonToList
  = Atom

singletonFromList
  :: FromList '[a] a
singletonFromList
  = Atom

singletonFromSet
  :: FromSet '[a] a
singletonFromSet
  = FromSet singletonConsumeN
            singletonFromList

singletonFromSuperset
  :: FromSuperset '[a] a
singletonFromSuperset
  = FromSuperset singletonConsumeN
                 singletonFromList
