{-# LANGUAGE ConstraintKinds, GADTs, DataKinds, PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances, ViewPatterns #-}
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
infixr 3 ***
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

infixr 1 `Cons2`
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

-- One problem with that attempt is that we can write the same identity
-- morphism in more than one way:
--
-- > Par2 Id2 Id2 `Cons2` Par2 Id2 Id2 `Cons2` Nil2 !=
-- > Par2 Id2 Id2 `Cons2` Nil2 !=
-- > Nil2
--
-- Clearly, we should not allow 'Layer2' values containing only 'Id2's. We do
-- do need to be able to represent @Par2 (Embed2 f) Id2@,
-- @Par2 Id2 (Embed2 g)@, and @Par2 (Embed2 f) (Embed2 g)@, but we don't want
-- to support @Par2 Id2 Id2@. One way to do that is to split the 'Par2'
-- constructor into four pieces, one for each combination of (the left argument
-- is 'Id2', the left argument is not 'Id2') x (the right argument is 'Id2',
-- the right argument is not 'Id2'), and to drop the unwanted piece in which
-- both arguments are 'Id2'.
--
-- Here is a third attempt which uses that approach:

infixr 1 `Cons3`
data FreeBif3 k a b where
  Nil3  :: FreeBif3 k a a
  Cons3 :: Layer3 k a b -> FreeBif3 k b c -> FreeBif3 k a c

data Layer3 k a b where
  Embed3     :: k a b -> Layer3 k a b
  LeftSide3  :: Layer3 k a1 b1                   -> Layer3 k (a1, x)  (b1, x)
  RightSide3 ::                   Layer3 k a2 b2 -> Layer3 k (x,  a2) (x,  b2)
  BothSides3 :: Layer3 k a1 b1 -> Layer3 k a2 b2 -> Layer3 k (a1, a2) (b1, b2)

instance Category (FreeBif3 k) where
  id = Nil3
  (.) = flip go
    where
      go :: FreeBif3 k a b -> FreeBif3 k b c -> FreeBif3 k a c
      go Nil3        h = h
      go (Cons3 f g) h = Cons3 f (go g h)

instance Bif (FreeBif3 k) where
  Nil3         *** Nil3         = Nil3
  Cons3 f1 fs1 *** Cons3 f2 fs2 = Cons3 (BothSides3 f1 f2)  (fs1  *** fs2)
  Nil3         *** Cons3 f2 fs2 = Cons3 (RightSide3    f2)  (Nil3 *** fs2)
  Cons3 f1 fs1 *** Nil3         = Cons3 (LeftSide3  f1)     (fs1  *** Nil3)

-- This is a pretty good attempt! It satisfies most of the laws:
--
-- > id >>> f = f = f >>> id
-- > (f >>> g) >>> h = f >>> (g >>> h)
-- > id *** id = id
--
-- But it doesn't satisfy this one:
--
-- > (f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)
-- > LeftSide3 f `Cons3` RightSide3 g `Cons3` Nil3 !=
-- > BothSides3 f g `Cons3` Nil3 !=
-- > RightSide3 g `Cons3` LeftSide3 f `Cons3` Nil3
--
-- To solve the problem, let's add a normalization step which compresses values
-- like @LeftSide3 f `Cons3` RightSide3 g `Cons3` Nil3@
-- and @RightSide3 g `Cons3` LeftSide3 f `Cons3` Nil3@
-- into @BothSides3 f g `Cons3` Nil3@.

infixr 1 `Cons4`
data FreeBif4 k a b where
  Nil4  :: FreeBif4 k a a
  Cons4 :: Layer4 k a b -> FreeBif4 k b c -> FreeBif4 k a c

data Layer4 k a b where
  Embed4     :: k a b -> Layer4 k a b
  LeftSide4  :: Layer4 k a1 b1                   -> Layer4 k (a1, x)  (b1, x)
  RightSide4 ::                   Layer4 k a2 b2 -> Layer4 k (x,  a2) (x,  b2)
  BothSides4 :: Layer4 k a1 b1 -> Layer4 k a2 b2 -> Layer4 k (a1, a2) (b1, b2)

instance Category (FreeBif4 k) where
  id = Nil4
  (.) = flip go
    where
      go :: FreeBif4 k a b -> FreeBif4 k b c -> FreeBif4 k a c
      go Nil4        h = h
      go (Cons4 f g) h = cons4 f (go g h)

instance Bif (FreeBif4 k) where
  Nil4         *** Nil4         = Nil4
  Cons4 f1 fs1 *** Cons4 f2 fs2 = cons4 (BothSides4 f1 f2)  (fs1  *** fs2)
  Nil4         *** Cons4 f2 fs2 = cons4 (RightSide4    f2)  (Nil4 *** fs2)
  Cons4 f1 fs1 *** Nil4         = cons4 (LeftSide4  f1)     (fs1  *** Nil4)

cons4 :: Layer4 k a b -> FreeBif4 k b c -> FreeBif4 k a c
cons4 f              Nil4                       = Cons4 f Nil4
cons4 (LeftSide4  f) (Cons4 (RightSide4 g) fs)  = Cons4 (BothSides4 f g) fs
cons4 (RightSide4 g) (Cons4 (LeftSide4 f) fs)   = Cons4 (BothSides4 f g) fs
cons4 (LeftSide4  f) (Cons4 (LeftSide4 g) fs)   = case cons4 f (cons4 g Nil4) of
  Cons4 fg Nil4 -> LeftSide4 fg `Cons4` fs
  _             -> LeftSide4 f  `Cons4` LeftSide4 g `Cons4` fs
cons4 (RightSide4  f) (Cons4 (RightSide4 g) fs) = case cons4 f (cons4 g Nil4) of
  Cons4 fg Nil4 -> RightSide4 fg `Cons4` fs
  _             -> RightSide4 f  `Cons4` RightSide4 g `Cons4` fs

-- That should work... I think? I almost forgot to add the last two cases,
-- which are required to normalize
-- @LeftSide4 (LeftSide4 f) `cons4` LeftSide4 (RightSide4 g) `cons4` Nil4@
-- to @LeftSide4 (BothSides4 f g) `Cons4` Nil4`.
--
-- Another problem is that even though the '(>>>)' and '(***)' normalize their
-- output in order to satisfy the laws, non-normalized morphisms are still
-- valid 'FreeBif4' values, so we again have too many morphisms. It's not
-- enough to replace @LeftSide4 f `Cons4` RightSide4 g `Cons4` Nil4@ and
-- @RightSide4 g `Cons4` LeftSide4 f `Cons4` Nil4@ with a normalized version,
-- we must make those unrepresentable!

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
