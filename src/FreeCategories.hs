{-# LANGUAGE ConstraintKinds, GADTs, DataKinds, PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances #-}
module FreeCategories where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)


data Parent a
  = L  a  -- ^ left  child of parent
  | R  a  -- ^ right child of parent
  | NA a  -- ^ n/a, not a children

data Tree a
  = Leaf (Parent a)
  | Branch (Tree a) (Tree a)

type family ReparentLeaf (p  :: k -> Parent k)
                         (ta :: Tree k)
                      :: Tree k where
  ReparentLeaf p ('Leaf ('NA a))   = 'Leaf (p a)
  ReparentLeaf _ ('Branch ta1 ta2) = 'Branch ta1 ta2

data SplitTree (a  :: Type)
               (tb :: Tree Type) where
  NoSplit :: SplitTree a ('Leaf ('NA a))
  Split   :: SplitTree a1 tb1
          -> SplitTree a2 tb2
          -> SplitTree (a1,a2) (Branch (ReparentLeaf 'L tb1)
                                       (ReparentLeaf 'R tb2))


-- divide @as@ into two parts, @as1@ and @as2@, which can be concatenated to obtain @as@ back
data SplitList (as  :: [k])
               (as1 :: [k])
               (as2 :: [k]) where
  Here  :: SplitList abc         '[]       abc
  There :: SplitList bcde        bc        de
        -> SplitList (a ': bcde) (a ': bc) de

-- is @a@ an element of @as@?
data Elem (as :: [k])
          (a  :: k) where
  Elem :: SplitList abcde ab (c ': de)
       -> Elem abcde c

-- can we obtain @as2@ by deleting a prefix and a suffix from @as1@?
data Substring (as1 :: [k])
               (as2 :: [k]) where
  Substring :: SplitList abcdef ab cdef
            -> SplitList cdef   cd ef
            -> Substring abcdef cd

-- can we obtain @as2@ by deleting some elements from @as1@?
data Subsequence (as1 :: [k])
                 (as2 :: [k]) where
  Done :: Subsequence '[]          '[]
  Skip :: Subsequence bcdef        ce
       -> Subsequence (a ': bcdef) ce
  Keep :: Subsequence bcdef        ce
       -> Subsequence (a ': bcdef) (a ': ce)

-- can we obtain @as2@ by using each element of @as1@ zero or more times in some order?
data Multisubset (as1 :: [k])
                 (as2 :: [k]) where
  MultiNil  :: Multisubset abc '[]
  MultiCons :: Elem abcdef b
            -> Multisubset abcdef aafbba
            -> Multisubset abcdef (b ': aafbba)

-- can we obtain @as2@ by reordering the elements of @as1@?
data Permutation (as1 :: [k])
                 (as2 :: [k]) where
  -- TODO

-- can we obtain @as2@ by deleting some elements of @as1@ and reordering the rest?
data Subset (as1 :: [k])
            (as2 :: [k]) where
  Subset :: Subsequence abcde bd
         -> Permutation bd db
         -> Subset abcde db


-- the M stands for "morphism"
data MList t k pas pbs where
  MNil  :: t pas pbs
        => MList t k pas pbs
  MCons :: t tb tb'
        => SplitTree a ta
        -> k a b
        -> SplitTree b tb
        -> MList t k tb' tc
        -> MList t k ta tc

data MNonEmpty t k ta tb where
  MNonEmpty :: t tb tb'
            => SplitTree a ta
            -> k a b
            -> SplitTree b tb
            -> MList t k tb' tc
            -> MNonEmpty t k ta tc


type family Concat (as1 :: [k])
                   (as2 :: [k])
                :: [k] where
  Concat '[]        as2 = as2
  Concat (a ': as1) as2 = a ': Concat as1 as2

type family Flatten (ta :: Tree k)
                 :: [Parent k] where
  Flatten ('Leaf pa)        = '[pa]
  Flatten ('Branch ta1 ta2) = Concat (Flatten ta1)
                                     (Flatten ta2)

type family MapUnparent (pas :: [Parent k])
                     :: [k] where
  MapUnparent '[]          = '[]
  MapUnparent (p a ': pas) = a ': MapUnparent pas


type family HasSuperfluousSplits (pas :: [Parent k])
                                 (pbs :: [Parent k])
                              :: Bool where
  HasSuperfluousSplits '[] '[]  = 'False
  HasSuperfluousSplits ('L _ ': 'R _ ': pas) ('L _ ': 'R _ ': pbs) = 'True
  HasSuperfluousSplits (_ ': pas) (_ ': pbs) = HasSuperfluousSplits pas pbs
  -- undefined if the lists have different lengths


-- -- bifunctorial category
-- data BifTransition a b where
--   BifTransition :: TreeHasSuperfluousSplits ta tb ~ 'False
--                 => SplitTree a ta
--                 -> SplitTree b tb
--                 -> BifTransition a b
-- 
-- type FreeBif k = MList BifTransition (MEmbed k)
-- 
-- instance Category BifTransition where
--   id = BifTransition NoSplit NoSplit
--   BifTransition sb' sc . BifTransition sa sb =
--     BifTransition sa sc
-- 
-- 
-- twoMorphisms :: k (a1,a2) (b1,b2) -> k (b1,b2) (c1,c2) -> FreeBif k (a1,a2) (c1,c2)
-- twoMorphisms f g = MCons (BifTransition NoSplit NoSplit) (MWhole f)
--                  $ MCons (BifTransition NoSplit NoSplit) (MWhole g)
--                  $ MNil (BifTransition NoSplit NoSplit)





-- semigroupoid
-- category
-- bifunctorial
-- associative
-- monoidal
-- linear
-- affine
-- cartesian

--type Permutation as bs


main :: IO ()
main = putStrLn "typechecks."
