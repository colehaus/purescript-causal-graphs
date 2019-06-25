module Data.Graph.Causal.Utility where

import Prelude

import Data.Array as Array
import Data.List (List(..))
import Data.List.NonEmpty (NonEmptyList(..))
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (uncurry)
import Data.TwoSet (TwoSet(..))
import Data.TwoSet as TwoSet

-- Returns value before first occurrence of k
before :: forall k. Eq k => k -> NonEmptyList k -> Maybe k
before a (NonEmptyList (x :| Cons y zs))
  | y == a = Just x
  | otherwise = before a (NonEmptyList $ y :| zs)
before a _ = Nothing

-- Returns value after first occurrence of k
after :: forall k. Eq k => k -> NonEmptyList k -> Maybe k
after a (NonEmptyList (x :| Cons y zs))
  | x == a = Just y
  | otherwise = after a (NonEmptyList $ y :| zs)
after a _ = Nothing

distinctTwoSets :: forall a. Ord a => Set a -> Set (TwoSet a)
distinctTwoSets as =
  Set.filter (uncurry (/=) <<< TwoSet.toTuple) <<< Set.fromFoldable $
  MkTwoSet <$> Array.fromFoldable as <*> Array.fromFoldable as

