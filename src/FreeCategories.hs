{-# LANGUAGE GADTs, DataKinds, PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances #-}
module FreeCategories where

import Data.Kind (Type)


data Parent a
  = L  a  -- ^ left  child of parent
  | R  a  -- ^ right child of parent

data Subtree a
  = Leaf (Parent a)
  | Branch (Subtree a) (Subtree a)

data Tree a
  = Singleton a
  | Root (Subtree a) (Subtree a)

type family AnnotateParent (p  :: k -> Parent k)
                           (ta :: Tree k)
                        :: Subtree k where
  AnnotateParent p ('Singleton a)  = 'Leaf (p a)
  AnnotateParent _ ('Root ta1 ta2) = 'Branch ta1 ta2

type family MkBranch (ta1 :: Tree k)
                     (ta2 :: Tree k)
                  :: Tree k where
  MkBranch ta1 ta2 = 'Root (AnnotateParent 'L ta1)
                           (AnnotateParent 'R ta2)

data SplitTree (a  :: Type)
               (tb :: Tree Type) where
  NoSplit :: SplitTree a ('Singleton a)
  Split   :: SplitTree a1 tb1
          -> SplitTree a2 tb2
          -> SplitTree (a1,a2) (MkBranch tb1 tb2)


-- the M stands for "morphism"
data MList t k a b where
  MNil  :: t a a'
        -> MList t k a a'
  MCons :: t a a'
        -> k a' b
        -> MList t k b c
        -> MList t k a c

data MNonEmpty t k a b where
  MNonEmpty :: t a a'
            -> k a' b
            -> MList t k b c
            -> MNonEmpty t k a c


type family Concat (as1 :: [k])
                   (as2 :: [k])
                :: [k] where
  Concat '[]        as2 = as2
  Concat (a ': as1) as2 = a ': Concat as1 as2

type family FlattenSubtree (ta :: Subtree k)
                        :: [Parent k] where
  FlattenSubtree ('Leaf pa)        = '[pa]
  FlattenSubtree ('Branch ta1 ta2) = Concat (FlattenSubtree ta1)
                                            (FlattenSubtree ta2)

type family MapUnparent (pas :: [Parent k])
                     :: [k] where
  MapUnparent '[]          = '[]
  MapUnparent (p a ': pas) = a ': MapUnparent pas

type family FlattenTree (ta :: Tree k)
                     :: [k] where
  FlattenTree ('Singleton a)  = '[a]
  FlattenTree ('Root ta1 ta2) = Concat (MapUnparent (FlattenSubtree ta1))
                                       (MapUnparent (FlattenSubtree ta2))


type family ListHasSuperfluousSplits (pas :: [Parent k])
                                     (pbs :: [Parent k])
                                  :: Bool where
  ListHasSuperfluousSplits '[] '[]  = 'False
  ListHasSuperfluousSplits ('L _ ': 'R _ ': pas) ('L _ ': 'R _ ': pbs) = 'True
  ListHasSuperfluousSplits (_ ': pas) (_ ': pbs) = ListHasSuperfluousSplits pas pbs
  -- undefined if the lists have different lengths

type family TreeHasSuperfluousSplits (ta :: Tree k)
                                     (tb :: Tree k)
                                  :: Bool where
  TreeHasSuperfluousSplits ('Singleton _)  ('Singleton _)  = 'False
  TreeHasSuperfluousSplits ('Root ta1 ta2) ('Root tb1 tb2) =
    ListHasSuperfluousSplits (Concat (FlattenSubtree ta1) (FlattenSubtree ta2))
                             (Concat (FlattenSubtree tb1) (FlattenSubtree tb2))
  -- undefined if the lists have a different number of leaves


-- type FreeSemi = MNonEmpty 

--data Embed k a b where

-- bifunctorial category
data BifTransition a b where
  BifTransition :: TreeHasSuperfluousSplits ta tb ~ 'False
                => SplitTree a ta
                -> SplitTree b tb
                -> BifTransition a b

type FreeBif = MList BifTransition


twoMorphisms :: k (a1,a2) (b1,b2) -> k (b1,b2) (c1,c2) -> FreeBif k (a1,a2) (c1,c2)
twoMorphisms f g = MCons (BifTransition NoSplit NoSplit) f
                 $ MCons (BifTransition NoSplit NoSplit) g
                 $ MNil (BifTransition NoSplit NoSplit)


data PickOne (as :: [k])
             (b  :: k) where
  Here  :: PickOne (a ': as) a
  There :: PickOne as b -> PickOne (a ': as) b

data PickMany (as :: [k])
              (bs :: [k]) where
  PickNil  :: PickMany as '[]
  PickCons :: PickOne as b
           -> PickMany as bs
           -> PickMany as (b ': bs)


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
