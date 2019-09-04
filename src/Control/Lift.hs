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
import           Data.Functor.Compose (Compose)
import           Data.Coerce (Coercible, coerce)

-- | Lift any pure function over any @Applicative@ stack.
--
-- >>> liftAll @[[Int]] @Int (+) [[1]] [[2]]
-- [[3]]
--
-- >>> liftAll @(Maybe [String]) @String (,,) (Just ["one"]) (Just ["two"]) (Just ["three", "four"])
-- Just [("one","two","three"),("one","two","four")]
liftAll :: forall w a b d n g.
        ( CountArgs b ~ n
        , Applicative g
        , EmbedDepth a w ~ d
        , ComposeUntil d w a ~ g a
        , Applyable n d g b
        , Coercible w (g a)
        )
        => (a -> b) -> w -> App n d g b
liftAll f = apply @n @d . fmap @g f . coerce

-- | Apply an @Applicative@ effect across any @Traversable@ stack.
--
-- >>> traverseAll @(Maybe [Int]) @Int print (Just [1,2,3])
-- 1
-- 2
-- 3
-- Just [(),(),()]
traverseAll :: forall w a b d f g res.
            ( EmbedDepth a w ~ d
            , ComposeUntil d w a ~ g a
            , FlattenUntil d (g b) b ~ res
            , Applicative f
            , Traversable g
            , Coercible res (g b)
            , Coercible w (g a)
            )
            => (a -> f b) -> w -> f res
traverseAll f = fmap coerce . traverse @g f . coerce

-- | Apply an @Applicative@ effect across any @Foldable@ stack, discarding the result.
--
-- >>> traverseAll_ @[Maybe [Int]] @Int print [Just [1,2,3], Nothing, Just [4]]
-- 1
-- 2
-- 3
-- 4
traverseAll_ :: forall w a b d f g.
             ( EmbedDepth a w ~ d
             , ComposeUntil d w a ~ g a
             , Foldable g
             , Applicative f
             , Coercible w (g a)
             )
             => (a -> f b) -> w -> f ()
traverseAll_ f = traverse_ @g f . coerce

-- | Map over any @Functor@ stack.
--
-- >>> fmapAll @[Either String Int] @Int (*2) [Right 3, Left "nope", Right 5]
-- [Right 6,Left "nope",Right 10]
fmapAll :: forall w a b d f res.
        ( EmbedDepth a w ~ d
        , FlattenUntil d (f b) b ~ res
        , ComposeUntil d w a ~ f a
        , Functor f
        , Coercible w (f a)
        , Coercible res (f b)
        )
        => (a -> b) -> w -> res
fmapAll f = coerce . fmap @f f . coerce

-- | Turn every element of a @Foldable@ stack into a @Monoid@ then combine them.
--
-- >>> foldMapAll @[Maybe[Int]] @Int Sum [Just [1,2,3], Nothing, Just [4,5]]
-- Sum {getSum = 15}
foldMapAll :: forall w a m d f.
           ( EmbedDepth a w ~ d
           , ComposeUntil d w a ~ f a
           , Foldable f
           , Monoid m
           , Coercible w (f a)
           )
           => (a -> m) -> w -> m
foldMapAll f = foldMap @f f . coerce

-- | Right fold over any @Foldable@ stack.
--
-- >>> foldrAll @[[Int]] @Int (\x acc -> acc ++ show x) [] [[1,2],[3]]
-- "321"
foldrAll :: forall w a b d f res.
         ( EmbedDepth a w ~ d
         , ComposeUntil d w a ~ f a
         , Foldable f
         , Coercible w (f a)
         )
         => (a -> b -> b) -> b -> w -> b
foldrAll f b = foldr @f f b . coerce

-- | Left fold over any @Foldable@ stack.
--
-- >>> foldlAll @[[Int]] @Int (\acc x -> acc ++ show x) [] [[1,2],[3]]
-- "123"
foldlAll :: forall w a b d f res.
         ( EmbedDepth a w ~ d
         , ComposeUntil d w a ~ f a
         , Foldable f
         , Coercible w (f a)
         )
         => (b -> a -> b) -> b -> w -> b
foldlAll f b = foldl @f f b . coerce

-- | Strict left fold over any @Foldable@ stack.
foldlAll' :: forall w a b d f res.
          ( EmbedDepth a w ~ d
          , ComposeUntil d w a ~ f a
          , Foldable f
          , Coercible w (f a)
          )
         => (b -> a -> b) -> b -> w -> b
foldlAll' f b = foldl' @f f b . coerce

--------------------------------------------------------------------------------
-- Type classes
--------------------------------------------------------------------------------

class (CountArgs f ~ n) => Applyable n d g f where
  apply :: g f -> App n d g f

instance ( CountArgs f ~ Z
         , Coercible (FlattenUntil d (g f) f) (g f)
         ) => Applyable Z d g f where
  apply = coerce
  {-# INLINE apply #-}

instance ( Applyable n d g b
         , FlattenUntil d (g a) a ~ w
         , ComposeUntil d w a ~ g a
         , Applicative g
         , Coercible w (g a)
         ) => Applyable (S n) d g (a -> b) where
  apply gf = apply @n @d @g @b . (gf <*>) . coerce
  {-# INLINE apply #-}

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

