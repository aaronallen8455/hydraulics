{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE UndecidableInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Control.Lift
-- Copyright   :  (C) 2019 Aaron Allen
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Aaron Allen <aaronallen8455@gmail.com>
-- Stability   :  provisional
-- Portability :  TypeFamilies, DataKinds, TypeApplications
--
--------------------------------------------------------------------------------
module Control.Lift
  ( liftAll
  , traverseAll
  , traverseAll_
  , sequenceAll
  , sequenceAll_
  , fmapAll
  , foldMapAll
  , foldrAll
  , foldlAll
  , foldlAll'
  , concatAll
  , module Data.Functor.Compose
  ) where

import           Data.Foldable (foldl', sequence_, traverse_)
import           Data.Functor.Compose (Compose(..))
import           Data.Coerce (Coercible, coerce)

-- | Lift any pure function over any @Applicative@ stack.
--
-- >>> liftAll @[[()]] (+) [[1::Int]] [[2]]
-- [[3]]
--
-- >>> liftAll @(Maybe [()]) (,,) (Just ["one"]) (Just ["two"]) (Just ["three", "four"])
-- Just [("one","two","three"),("one","two","four")]
liftAll :: forall s f g d n.
        ( CountArgs f ~ n
        , Applicative g
        , EmbedDepth () s ~ d
        , ComposeUntil d s ~ g ()
        , Applyable n d g f
        , Coercible s (g ())
        )
        => f -> App n d g f
liftAll = apply @n @d . pure @g

-- | Apply an @Applicative@ effect across any @Traversable@ stack.
--
-- >>> traverseAll @(Maybe [()]) print (Just [1,2,3])
-- 1
-- 2
-- 3
-- Just [(),(),()]
traverseAll :: forall s a b d f g res sa.
            ( EmbedDepth () s ~ d
            , ComposeUntil d s ~ g ()
            , FlattenUntil d (g b) ~ res
            , FlattenUntil d (g a) ~ sa
            , Applicative f
            , Traversable g
            , Coercible res (g b)
            , Coercible sa (g a)
            )
            => (a -> f b) -> sa -> f res
traverseAll f = fmap coerce . traverse @g f . coerce

-- | Apply an @Applicative@ effect across any @Foldable@ stack, discarding the result.
--
-- >>> traverseAll_ @[Maybe [()]] print [Just [1,2,3], Nothing, Just [4]]
-- 1
-- 2
-- 3
-- 4
traverseAll_ :: forall s a b sa d f g.
             ( EmbedDepth () s ~ d
             , ComposeUntil d s ~ g ()
             , ComposeUntil d sa ~ g a
             , Foldable g
             , Applicative f
             , Coercible sa (g a)
             )
             => (a -> f b) -> sa -> f ()
traverseAll_ f = traverse_ @g f . coerce @sa @(g a)

-- | Run the @Applicative@ effects embedded in a @Traversable@ stack.
--
-- >>> sequenceAll @[Maybe ()] [Just (print 1), Nothing, Just (print 2)]
-- 1
-- 2
-- [Just (), Nothing, Just ()]
sequenceAll :: forall s a d f g res sfa.
            ( EmbedDepth () s ~ d
            , ComposeUntil d s ~ g ()
            , FlattenUntil d (g (f a)) ~ sfa
            , FlattenUntil d (g a) ~ res
            , Applicative f
            , Traversable g
            , Coercible sfa (g (f a))
            , Coercible res (g a)
            )
            => sfa -> f res
sequenceAll = traverseAll @s @(f a) id

-- | Run the @Applicative@ effects embedded in a @Foldable@ stack, discarding the result.
--
-- >>> sequenceAll_ @(Either () [()]) $ Right [print 1]
-- 1
sequenceAll_ :: forall s a d f g sfa.
             ( EmbedDepth () s ~ d
             , ComposeUntil d s ~ g ()
             , ComposeUntil d sfa ~ g (f a)
             , Applicative f
             , Foldable g
             , Coercible sfa (g (f a))
             )
             => sfa -> f ()
sequenceAll_ = traverseAll_ @s id

-- | Map over any @Functor@ stack.
--
-- >>> fmapAll @[Either String ()] (*2) [Right 3, Left "nope", Right 5]
-- [Right 6,Left "nope",Right 10]
fmapAll :: forall s sa a b d f res.
        ( EmbedDepth () s ~ d
        , FlattenUntil d (f b) ~ res
        , FlattenUntil d (f a) ~ sa
        , ComposeUntil d s ~ f ()
        , Functor f
        , Coercible sa (f a)
        , Coercible res (f b)
        )
        => (a -> b) -> sa -> res
fmapAll f = coerce . fmap @f f . coerce

-- | Turn every embeded element of a @Foldable@ stack into a @Monoid@ then combine them.
--
-- >>> foldMapAll @[Maybe[()]] Sum [Just [1,2,3], Nothing, Just [4,5]]
-- Sum {getSum = 15}
foldMapAll :: forall s sa a m d f.
           ( EmbedDepth () s ~ d
           , ComposeUntil d sa ~ f a
           , Foldable f
           , Monoid m
           , Coercible sa (f a)
           )
           => (a -> m) -> sa -> m
foldMapAll f = foldMap @f f . coerce

-- | Right fold over any @Foldable@ stack.
--
-- >>> foldrAll @[[()]] (\x acc -> acc ++ show x) [] [[1,2],[3]]
-- "321"
foldrAll :: forall s sa a b d f res.
         ( EmbedDepth () s ~ d
         , ComposeUntil d sa ~ f a
         , Foldable f
         , Coercible sa (f a)
         )
         => (a -> b -> b) -> b -> sa -> b
foldrAll f b = foldr @f f b . coerce

-- | Left fold over any @Foldable@ stack.
--
-- >>> foldlAll @[[()]] (\acc x -> acc ++ show x) [] [[1,2],[3]]
-- "123"
foldlAll :: forall s sa a b d f res.
         ( EmbedDepth () s ~ d
         , ComposeUntil d sa ~ f a
         , Foldable f
         , Coercible sa (f a)
         )
         => (b -> a -> b) -> b -> sa -> b
foldlAll f b = foldl @f f b . coerce

-- | Strict left fold over any @Foldable@ stack.
foldlAll' :: forall s sa a b d f res.
          ( EmbedDepth () s ~ d
          , ComposeUntil d sa ~ f a
          , Foldable f
          , Coercible sa (f a)
          )
         => (b -> a -> b) -> b -> sa -> b
foldlAll' f b = foldl' @f f b . coerce

-- | Concatenates any @Foldable@ stack down to a list.
--
-- >>> concatAll @(Maybe [[()]]) $ Just [[2], [3,4]]
-- [2,3,4]
concatAll :: forall s sa a b d f res.
          ( EmbedDepth [()] s ~ d
          , ComposeUntil d sa ~ f [a]
          , Foldable f
          , Coercible sa (f [a])
          )
         => sa -> [a]
concatAll = concat @f . coerce

--------------------------------------------------------------------------------
-- Type classes
--------------------------------------------------------------------------------

class (CountArgs f ~ n) => Applyable n d g f where
  apply :: g f -> App n d g f

instance ( CountArgs f ~ Z
         , Coercible (FlattenUntil d (g f)) (g f)
         ) => Applyable Z d g f where
  apply = coerce
  {-# INLINE apply #-}

instance ( Applyable n d g b
         , FlattenUntil d (g a) ~ s
         , ComposeUntil d s ~ g a
         , Applicative g
         , Coercible s (g a)
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

type family EmbedDepth a s :: Nat where
  EmbedDepth a a = Z
  EmbedDepth a (s b) = S (EmbedDepth a b)

type family App (n :: Nat) (d :: Nat) g x where
  App (S n) d g (a -> b) = FlattenUntil d (g a) -> App n d g b
  App Z d g a = FlattenUntil d (g a)

type family Embed f g where
  Embed f (g a) = Compose f g a
  Embed f a = f a

type family ComposeUntil n f where
  ComposeUntil Z a = a
  ComposeUntil (S Z) (f a) = f a
  ComposeUntil (S n) (f b) = Embed f (ComposeUntil n b)

type family Extract f g where
  Extract f (Compose g h a) = f (g (h a))
  Extract f a = f a

type family FlattenUntil n f where
  FlattenUntil Z a = a
  FlattenUntil (S Z) (f a) = f a
  FlattenUntil (S n) (Compose f g a) = f (FlattenUntil n (g a))

