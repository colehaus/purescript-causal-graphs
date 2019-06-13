module Data.Graph.Causal.Utility where

import Prelude

import Data.Array as Array
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (uncurry)
import Data.TwoSet (TwoSet(..))
import Data.TwoSet as TwoSet

-- Returns value before first occurrence of k
before :: forall k. Eq k => k -> List k -> Maybe k
before a (Cons x (Cons y zs))
  | y == a = Just x
  | otherwise = before a (Cons y zs)
before a _ = Nothing

-- Returns value after first occurrence of k
after :: forall k. Eq k => k -> List k -> Maybe k
after a (Cons x (Cons y zs))
  | x == a = Just y
  | otherwise = after a (Cons y zs)
after a _ = Nothing

distinctTwoSets :: forall a. Ord a => Set a -> Set (TwoSet a)
distinctTwoSets as =
  Set.filter (uncurry (/=) <<< TwoSet.toTuple) <<< Set.fromFoldable $
  MkTwoSet <$> Array.fromFoldable as <*> Array.fromFoldable as

