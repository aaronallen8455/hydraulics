{-# LANGUAGE DataKinds
           , TypeFamilies
           , MultiParamTypeClasses
           , FlexibleInstances
           , ScopedTypeVariables
           , TypeApplications
           , AllowAmbiguousTypes
           , UndecidableInstances
#-}
module Control.Lift
  ( liftGen
  ) where

import Data.Functor.Compose (Compose(..))

liftGen :: forall w n a b g depth.
          ( CountArgs b ~ n
          , Applicative g
          , EmbedDepth a w ~ depth
          , ComposeUntil depth w a ~ g a
          , Applyable n depth g b
          , Comp depth w a
          )
       => (a -> b) -> w -> App2 n depth g b
liftGen f = apply @n @depth @g . fmap f . comp @depth @w @a

class (CountArgs f ~ n) => Applyable n d g f where
  apply :: g f -> App2 n d g f

instance ( CountArgs f ~ Z
         , Decomp d (g f) f
         ) => Applyable Z d g f where
  apply = decomp @d @(g f) @f

instance ( Applyable n d g b
         , FlattenUntil d (g a) a ~ w
         , ComposeUntil d w a ~ g a
         , Applicative g
         , Comp d w a
         ) => Applyable (S n) d g (a -> b) where
  apply gf = apply @n @d @g @b . (gf <*>) . comp @d @w @a

class EmbedDepth a f ~ n => Comp n f a where
  comp :: f -> ComposeUntil n f a

instance Comp Z a a where
  comp = id

instance (EmbedDepth a (f a) ~ S Z) => Comp (S Z) (f a) a where
  comp = id

instance ( Comp (S n) g a
         , EmbedDepth a (f g) ~ S (S n)
         , ComposeUntil (S n) g a ~ w a
         , ComposeUntil (S (S n)) (f g) a ~ Compose f w a
         , Functor f
         ) => Comp (S (S n)) (f g) a where
  comp = Compose . fmap (comp @(S n) @g @a)

class EmbedDepth a (FlattenUntil n f a) ~ n => Decomp n f a where
  decomp :: f -> FlattenUntil n f a

instance Decomp Z a a where
  decomp = id

instance ( EmbedDepth a (FlattenUntil ('S 'Z) fa a) ~ S Z
         , FlattenUntil ('S 'Z) fa a ~ fa
         ) => Decomp (S Z) fa a where
  decomp = id

instance ( Decomp n (g a) a
         , FlattenUntil n (g a) a ~ w
         , FlattenUntil (S n) (Compose f g a) a ~ f w
         , EmbedDepth a (f w) ~ S n
         , Functor f
         ) => Decomp (S n) (Compose f g a) a where
  decomp = fmap (decomp @n @(g a) @a) . getCompose

data Nat = Z | S Nat

type family CountArgs f :: Nat where
  CountArgs (a -> b) = S (CountArgs b)
  CountArgs a = Z

type family EmbedDepth a w :: Nat where
  EmbedDepth a a = Z
  EmbedDepth a (w b) = S (EmbedDepth a b)

-- is the depth parameter needed?
type family App2 (n :: Nat) (d :: Nat) g x where
  App2 (S n) d g (a -> b) = FlattenUntil d (g a) a -> App2 n d g b
  App2 Z d g a = FlattenUntil d (g a) a

type family Embed f g where
  Embed f (g a) = Compose f g a

type family ComposeUntil n f a where
  ComposeUntil Z a a = a
  ComposeUntil (S Z) (f a) a = f a
  ComposeUntil (S n) (f b) a = Embed f (ComposeUntil n b a)

type family Extract f g where
  Extract f (Compose g h a) = f (g (h a))
  Extract f (g a) = f (g a)

type family FlattenUntil n f a where
  FlattenUntil Z a a = a
  FlattenUntil (S Z) (f a) a = f a
  FlattenUntil (S n) (Compose f g a) a = Extract f (FlattenUntil n (g a) a)

