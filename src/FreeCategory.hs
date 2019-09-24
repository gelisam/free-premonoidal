{-# LANGUAGE GADTs, RankNTypes #-}
-- In all of the modules in this project, we start with a "quiver"
-- @k :: * -> * -> *@ with one inhabitant per "generator" morphism. It is
-- called a "quiver" and not a "category" because @k@ is not required to have
-- identity morphisms nor to be closed under the composition of morphisms.
--
-- In each file, the goal is then to define a type constructor which adds some
-- extra morphisms to @k@ in order to define a category with some amount of
-- structure. In this file, we define a type constructor 'FreeCat' which adds
-- identity morphisms and composition morphisms, making @FreeCat k@ a proper
-- category. Later, 'FreeMonoidalCat' will add more morphisms, making
-- @FreeMonoidalCat k@ a monoidal category.
module FreeCategory where

import Prelude hiding (id, (.))

import Control.Category
import Data.Kind (Type)


-- One common mistake when defining this kind of generator is to define one
-- constructor for each morphism we want to add:

data CatAST k a b where
  EmbedAST   :: k a b -> CatAST k a b
  IdAST      :: CatAST k a a
  ComposeAST :: CatAST k a b -> CatAST k b c -> CatAST k a c

-- note that we don't require @Category k@; this is what would make this a
-- "free" category (if it was satisfying the laws; see below).
instance Category (CatAST k) where
  id = IdAST
  (.) = flip ComposeAST

-- The problem with that definition is that it does not satisfy the laws: we
-- want @id >>> f = f@ and @(f >>> g) >>> h = f >>> (g >>> h)@ to hold, but
-- @IdAST `ComposeAST` f@ and @f@ are not the same value, and neither are
-- @(f `ComposeAST` g) `ComposeAST` h@ and @f `ComposeAST` (g `ComposeAST` h)@.

-- Here is another unsatisfying definition:

newtype CatCPS k a b = CatCPS
  { unCatCPS :: forall r. Category r
             => (forall x y. k x y -> r x y)
             -> r a b
  }

instance Category (CatCPS k) where
  id = CatCPS $ \_ -> id
  f . g = CatCPS $ \embed
       -> unCatCPS f embed . unCatCPS g embed

-- The good thing about the above trick is that it always work, regardless of
-- the laws you have in mind for 'Category' (or whichever typeclass you use
-- this trick on). The bad thing about it is that it teaches you nothing about
-- the structure of the free category. The definition I really want is:

data FreeCat k a b where
  Nil  :: FreeCat k a a
  Cons :: k a b -> FreeCat k b c -> FreeCat k a c

instance Category (FreeCat k) where
  id = Nil
  (.) = flip go
    where
      go :: FreeCat k a b -> FreeCat k b c -> FreeCat k a c
      go Nil        h = h
      go (Cons f g) h = Cons f (go g h)

-- Wasn't that beautiful? A free category is simply a list of generator
-- morphisms! That's a very insightful definition, one which allows us to use
-- our intuition for e.g. thinking about a more efficient difference-list
-- representation, or something like 'Seq', or eliminating cycles, etc.
--
-- By contrast, the 'CatCPS' approach is opaque. It does not tell you anything
-- about the consequences of the laws, and in fact, it does not _really_
-- guarantee that the laws hold either. I could instantiate 'r' to a 'Category'
-- instance like 'CatAST' which doesn't satisfy the laws, and that would allow
-- me to distinguish between @f . id :: CatCPS k@ and @f :: CatCPS@. In fact,
-- the only reason 'CatCPS' always work is that it does not do any work, it
-- instead delegates all the work to the user: it can satisfy any law you think
-- 'Category' instances should follow _if_ the caller promises to only ever
-- instantiate 'r' with 'Category' instances which satisfy those laws. Meh.
