{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
module Control.Example where

import Control.Lift
import Data.Monoid
import Text.Read

a :: Either Bool [Int]
a = fmapAll @(Either Bool [()]) (+1) $ Right [2, 3::Int]

data Foo a = Foo a a a deriving Show

d :: forall a. Read a => IO (Maybe (Foo a))
d = liftAll' (pure $ Just ())
      Foo
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)

f :: IO (Either Int (Maybe [Foo Int]))
f = liftAll' (pure . Right . Just $ [()])
      Foo
        (pure . Right . traverse readMaybe . words =<< getLine)
        (pure . Right . traverse readMaybe . words =<< getLine)
        (pure . Right . traverse readMaybe . words =<< getLine)

g :: forall a. Read a => IO (Maybe (Foo a))
g = liftAll @(IO (Maybe ()))
      Foo
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)

data Bar = Bar Int String Double deriving Show

h :: IO (Maybe Bar)
h = liftAll @(IO (Maybe ()))
      Bar
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)
        (pure . readMaybe =<< getLine)

i :: Sum Int
i = foldMapAll @[[[()]]] Sum [[[23,25]]]

j :: Int
j = foldrAll @[Maybe ()] (+) (0 ::Int) [Just 3, Just 2]

k :: Int
k = foldlAll' @[Maybe ()] (+) (0 ::Int) [Just 3, Just 2]
