{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE UndecidableInstances  #-}
module Control.Lift
  ( liftAll
  , traverseAll
  , traverseAll_
  , fmapAll
  , foldMapAll
  , foldrAll
  , foldlAll
  , foldlAll'
  ) where

import           Data.Foldable (foldl', traverse_)
import           Data.Functor.Compose (Compose(..))

liftAll :: forall w a b d n g.
        ( CountArgs b ~ n
        , Applicative g
        , EmbedDepth a w ~ d
        , ComposeUntil d w a ~ g a
        , Applyable n d g b
        , Comp d w a
        )
        => (a -> b) -> w -> App n d g b
liftAll f = apply @n @d @g . fmap f . comp @d @w @a

traverseAll :: forall w a b d f g res.
            ( EmbedDepth a w ~ d
            , ComposeUntil d w a ~ g a
            , FlattenUntil d (g b) b ~ res
            , Applicative f
            , Traversable g
            , Decomp d (g b) b
            , Comp d w a
            )
            => (a -> f b) -> w -> f res
traverseAll f = fmap (decomp @d @(g b) @b) . traverse f . comp @d @w @a

traverseAll_ :: forall w a b d f g.
             ( EmbedDepth a w ~ d
             , ComposeUntil d w a ~ g a
             , Foldable g
             , Applicative f
             , Comp d w a
             )
             => (a -> f b) -> w -> f ()
traverseAll_ f = traverse_ f . comp @d @w @a

fmapAll :: forall w a b d f res.
        ( EmbedDepth a w ~ d
        , FlattenUntil d (f b) b ~ res
        , ComposeUntil d w a ~ f a
        , Decomp d (f b) b
        , Functor f
        , Comp d w a
        )
        => (a -> b) -> w -> res
fmapAll f = decomp @d @(f b) @b . fmap f . comp @d @w @a

foldMapAll :: forall w a m d f.
           ( EmbedDepth a w ~ d
           , ComposeUntil d w a ~ f a
           , Foldable f
           , Monoid m
           , Comp d w a
           )
           => (a -> m) -> w -> m
foldMapAll f = foldMap f . comp @d @w @a

foldrAll :: forall w a b d f res.
         ( EmbedDepth a w ~ d
         , ComposeUntil d w a ~ f a
         , Foldable f
         , Comp d w a
         )
         => (a -> b -> b) -> b -> w -> b
foldrAll f b = foldr f b . comp @d @w @a

foldlAll :: forall w a b d f res.
         ( EmbedDepth a w ~ d
         , ComposeUntil d w a ~ f a
         , Foldable f
         , Comp d w a
         )
         => (b -> a -> b) -> b -> w -> b
foldlAll f b = foldl f b . comp @d @w @a

foldlAll' :: forall w d a b f res.
          ( EmbedDepth a w ~ d
          , ComposeUntil d w a ~ f a
          , Foldable f
          , Comp d w a
          )
         => (b -> a -> b) -> b -> w -> b
foldlAll' f b = foldl' f b . comp @d @w @a

--------------------------------------------------------------------------------
-- Type classes
--------------------------------------------------------------------------------

class (CountArgs f ~ n) => Applyable n d g f where
  apply :: g f -> App n d g f

instance ( CountArgs f ~ Z
         , Decomp d (g f) f
         ) => Applyable Z d g f where
  apply = decomp @d @(g f) @f
  {-# INLINE apply #-}

instance ( Applyable n d g b
         , FlattenUntil d (g a) a ~ w
         , ComposeUntil d w a ~ g a
         , Applicative g
         , Comp d w a
         ) => Applyable (S n) d g (a -> b) where
  apply gf = apply @n @d @g @b . (gf <*>) . comp @d @w @a
  {-# INLINE apply #-}

class (EmbedDepth a f ~ n) => Comp n f a where
  comp :: f -> ComposeUntil n f a

instance Comp Z a a where
  comp = id
  {-# INLINE comp #-}

instance (EmbedDepth a (f a) ~ S Z) => Comp (S Z) (f a) a where
  comp = id
  {-# INLINE comp #-}

instance ( Comp (S n) g a
         , EmbedDepth a (f g) ~ S (S n)
         , ComposeUntil (S n) g a ~ w a
         , ComposeUntil (S (S n)) (f g) a ~ Compose f w a
         , Functor f
         ) => Comp (S (S n)) (f g) a where
  comp = Compose . fmap (comp @(S n) @g @a)
  {-# INLINE comp #-}

class EmbedDepth a (FlattenUntil n f a) ~ n => Decomp n f a where
  decomp :: f -> FlattenUntil n f a

instance Decomp Z a a where
  decomp = id
  {-# INLINE decomp #-}

instance ( EmbedDepth a (FlattenUntil ('S 'Z) fa a) ~ S Z
         , FlattenUntil ('S 'Z) fa a ~ fa
         ) => Decomp (S Z) fa a where
  decomp = id
  {-# INLINE decomp #-}

instance ( Decomp n (g a) a
         , FlattenUntil n (g a) a ~ w
         , FlattenUntil (S n) (Compose f g a) a ~ f w
         , EmbedDepth a (f w) ~ S n
         , Functor f
         ) => Decomp (S n) (Compose f g a) a where
  decomp = fmap (decomp @n @(g a) @a) . getCompose
  {-# INLINE decomp #-}

data Nat = Z | S Nat

--------------------------------------------------------------------------------
-- Type families
--------------------------------------------------------------------------------

type family CountArgs f :: Nat where
  CountArgs (a -> b) = S (CountArgs b)
  CountArgs a = Z

type family EmbedDepth a w :: Nat where
  EmbedDepth a a = Z
  EmbedDepth a (w b) = S (EmbedDepth a b)

type family App (n :: Nat) (d :: Nat) g x where
  App (S n) d g (a -> b) = FlattenUntil d (g a) a -> App n d g b
  App Z d g a = FlattenUntil d (g a) a

type family Embed f g where
  Embed f (g a) = Compose f g a
  Embed f a = f a

type family ComposeUntil n f a where
  ComposeUntil Z a a = a
  ComposeUntil (S Z) (f a) a = f a
  ComposeUntil (S n) (f b) a = Embed f (ComposeUntil n b a)

type family Extract f g where
  Extract f (Compose g h a) = f (g (h a))
  Extract f a = f a

type family FlattenUntil n f a where
  FlattenUntil Z a a = a
  FlattenUntil (S Z) (f a) a = f a
  FlattenUntil (S n) (Compose f g a) a = Extract f (FlattenUntil n (g a) a)

