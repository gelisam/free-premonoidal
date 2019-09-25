# free-categories

This is a free category:

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

It is "free" in the sense that it can take any `k` which does _not_ have a `Category` instance and add the identity and composition morphisms required in order to satisfy the requirements for `FreeCat k` to be a category.

That was pretty easy. But I want more. What about a free monoidal category? A free cartesian category? It turns out the additional structure required by these types of categories makes the problem a lot harder. This repo tracks my progress towards finding a free representation for those.

You might also be interested in [premonoidal](https://github.com/gelisam/premonoidal), in which I do the same for a related hierarchy of structured categories. The main difference is that in the structures explored in this repo, the law `(f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)` holds, whereas in `premonoidal`, it doesn't. This means this repo is for `(->)`-like categories, because if you have two pure functions, it doesn't matter in which order you apply them, whereas `premonoidal` is for `Kleisli m`-like categories, because if you have two actions, the order in which you apply them does affects the order in which their side-effects occur.
