{-# LANGUAGE ConstraintKinds, GADTs, DataKinds, PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances #-}
module FreeBifCategory where

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)

-- As a first step towards monoidal categories, let's define a typeclass for
-- categories which have a tensor @(,)@, but no identity object @()@ nor
-- morphisms witnessing the tensor's associativity @((a,b),c) <-> (a,(b,c))@,
-- just the ability to apply two morphisms in parallel, on both side of the
-- tensor.
--
-- laws:
--
-- > id *** id = id
-- > (f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)
class Category k => Bif k where
  (***) :: k a1 b1 -> k a2 b2 -> k (a1, a2) (b1, b2)

-- As usual, the incorrect way to do that is to define one constructor for each
-- morphism we want to add. Note that we want to add _both_ the identity and
-- composition morphisms from 'Category' _and_ the parallel morphisms from
-- 'Bif'.

data BifAST k a b where
  EmbedAST   :: k a b -> BifAST k a b
  IdAST      :: BifAST k a a
  ComposeAST :: BifAST k a b -> BifAST k b c -> BifAST k a c
  ParAST     :: BifAST k a1 b1 -> BifAST k a2 b2 -> BifAST k (a1, a2) (b1, b2)

instance Category (BifAST k) where
  id = IdAST
  (.) = flip ComposeAST

instance Bif (BifAST k) where
  (***) = ParAST

-- The problem with that first definition, as before, is that it does not
-- satisfy the laws. My intuition is that I again need something like a list,
-- except that each element of the list isn't a single generator morphism, it's
-- one or more of them acting in parallel on various parts of a nested pair.
-- Here is what that attempt looks like (attemt #2, hence the "2" suffix):

data FreeBif2 k a b where
  Nil2  :: FreeBif2 k a a
  Cons2 :: Layer2 k a b -> FreeBif2 k b c -> FreeBif2 k a c

data Layer2 k a b where
  Id2    :: Layer2 k a a
  Embed2 :: k a b -> Layer2 k a b
  Par2   :: Layer2 k a1 b1 -> Layer2 k a2 b2 -> Layer2 k (a1, a2) (b1, b2)

instance Category (FreeBif2 k) where
  id = Nil2
  (.) = flip go
    where
      go :: FreeBif2 k a b -> FreeBif2 k b c -> FreeBif2 k a c
      go Nil2        h = h
      go (Cons2 f g) h = Cons2 f (go g h)

instance Bif (FreeBif2 k) where
  Nil2         *** Nil2         = Nil2
  Cons2 f1 fs1 *** Cons2 f2 fs2 = Cons2 (Par2 f1  f2)  (fs1  *** fs2)
  Nil2         *** Cons2 f2 fs2 = Cons2 (Par2 Id2 f2)  (Nil2 *** fs2)
  Cons2 f1 fs1 *** Nil2         = Cons2 (Par2 f1  Id2) (fs1  *** Nil2)

-- This is a pretty good attempt! It satisfies most of the laws:
--
-- > id >>> f = f = f >>> id
-- > (f >>> g) >>> h = f >>> (g >>> h)
-- > id *** id = id
--
-- But it doesn't satisfy this one:
--
-- > (f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)
-- > Par2 f Id2 `Cons2` Par2 Id2 g `Cons2` Nil2 !=
-- > Par2 f g `Cons2` Nil2 !=
-- > Par2 Id2 g `Cons2` Par2 f Id2 `Cons2` Nil2
--
-- It also has too many reprentations for the same identity morphism:
--
-- > Par2 Id2 Id2 `Cons2` Par2 Id2 Id2 `Cons2` Nil2 !=
-- > Par2 Id2 Id2 `Cons2` Nil2 !=
-- > Nil2
--
-- To solve the problem, let's try making the following values unrepresentable:
--
-- > Par2 f Id2 `Cons2` Par2 Id2 g `Cons2` Nil2
-- > Par2 Id2 g `Cons2` Par2 f Id2 `Cons2` Nil2
-- > Par2 Id2 Id2 `Cons2` Par2 Id2 Id2 `Cons2` Nil2
-- > Par2 Id2 Id2 `Cons2` Nil2
--
-- Doing so will force the implementation of (***) to normalize its result,
-- thus ensuring that
--
-- > (Par2 f Id2 `Cons2` Nil2) *** (Id2 g `Cons2` Nil2) =
-- > Par2 f g `Cons2` Nil2


-- The rest of this file is not as well documented, but hopefully the
-- motivation is now clear.


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
