module Data.Graph.Causal.Utility where

import Prelude

import Data.Array as Array
import Data.Either (Either(..), hush)
import Data.Foldable (class Foldable, foldl, foldr)
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (uncurry)
import Data.TwoSet (TwoSet(..))
import Data.TwoSet as TwoSet

break :: forall a b c. (a -> b -> Either b c) -> a -> Either b c -> Either b c
break _ _ (Right b) = Right b
break f a (Left b) = f a b

-- These are probably a bit too cute but it was an experiment in
-- trying to make the fold out of composable pieces
history :: forall a b. (a -> Maybe a -> Maybe b) -> a -> Maybe a -> Either (Maybe a) b
history f a acc =
  case f a acc of
    Nothing -> Left (Just a)
    Just b -> Right b

-- Returns value before first occurrence of k
after :: forall f k. Eq k => Foldable f => k -> f k -> Maybe k
after a = hush <<< foldr (break <<< history $ f) (Left Nothing)
  where
    f curr prev
      | curr == a = prev
      | otherwise = Nothing

-- Returns value after first occurrence of k
before :: forall f k. Eq k => Foldable f => k -> f k -> Maybe k
before a = hush <<< foldl (flip (break <<< history $ f)) (Left Nothing)
  where
    f curr prev
      | curr == a = prev
      | otherwise = Nothing

distinctTwoSets :: forall a. Ord a => Set a -> Set (TwoSet a)
distinctTwoSets as =
  Set.filter (uncurry (/=) <<< TwoSet.toTuple) <<< Set.fromFoldable $
  MkTwoSet <$> Array.fromFoldable as <*> Array.fromFoldable as

powerSet :: forall a. Ord a => Set a -> Set (Set a)
powerSet =
  Set.fromFoldable <<< map Set.fromFoldable <<<
  List.filterM (const $ List.fromFoldable [true, false]) <<<
  List.fromFoldable
