# free-premonoidal

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

The kinds of categories I am interested in are:
1. premonoidal categories
2. symmetric premonoidal categories (linear types)
3. semicartesian premonoidal categories (affine types)
4. cartesian premonoidal categories (note: not _closed_ cartesian)

You might be more familiar with monoidal categories than premonoidal categories. The main difference between the two is that in a monoidal category, the law `(f *** id) >>> (id *** g) = f *** g = (id *** g) >>> (f *** id)` holds, whereas in a premonoidal category, `first f >>> second g` is not necessarily equal to `second g >>> first f`. For example, the law does not hold if `f` and `g` have side-effects.

I describe those kinds of categories in more details in [premonoidal](https://github.com/gelisam/premonoidal), a companion repo written in Agda with the more lofty goal of proving that each free structures I define in this repo is the mathematically-correct choice.
