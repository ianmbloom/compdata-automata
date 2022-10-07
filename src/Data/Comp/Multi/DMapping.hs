{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.DMapping
-- Copyright   :  (c) 2014 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides functionality to construct mappings from
-- positions in a functorial value.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.DMapping
    ( DNumbered (..)
    , unDNumbered
    , dNumber
    , HTraversable ()
    , DMapping (..)
    , lookupDNumMap) where

import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HTraversable

import Data.Type.Equality
import Data.GADT.Compare
import Unsafe.Coerce
import Control.Monad.State

import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap
import Data.Projection.Multi

-- | This type is used for numbering components of a functorial value.
data DNumbered a i = DNumbered (K Int i) (a i)

unDNumbered :: DNumbered a :-> a
unDNumbered (DNumbered _ x) = x


-- | This function numbers the components of the given functorial
-- value with consecutive integers starting at 0.
dNumber :: HTraversable f => f a :-> f (DNumbered a)
dNumber x = evalState (hmapM run x) 0 where
  run b = do n <- get
             put (n+1)
             return $ DNumbered (K n) b



infix 1 |->
infixr 0 &


class DMapping (m :: (* -> *) -> *) (key :: * -> *) | m -> key where
    -- | left-biased union of two mappings.
    (&) :: m v -> m v -> m v

    -- | This operator constructs a singleton mapping.
    (|->) :: key i -> v i -> m v

    -- | This is the empty mapping.
    empty :: m v

    -- | This function constructs the pointwise product of two maps each
    -- with a default value.
    prodMap :: (forall i . key i -> v1 i) -> (forall j . key j -> v2 j) -> m v1 -> m v2 -> m (v1 :^: v2)

    -- | Returns the value at the given key or returns the given
    -- default when the key is not an element of the map.
    findWithDefault :: a i -> key i -> m a -> a i


newtype DNumMap (k :: * -> *) v = DNumMap (DMap (K Int) v)

lookupDNumMap :: a i -> K Int i -> DNumMap t a -> a i
lookupDNumMap d k (DNumMap m) = DMap.findWithDefault d k m

instance DMapping (DNumMap k) (DNumbered k) where
    DNumMap m1 & DNumMap m2 = DNumMap (DMap.union m1 m2)
    DNumbered k _ |-> v = DNumMap $ DMap.singleton k v
    empty = DNumMap DMap.empty

    findWithDefault d (DNumbered i _) m = lookupDNumMap d i m

    prodMap defP defQ (DNumMap mapP) (DNumMap mapQ) =
      DNumMap $ undefined --  DMap.unionWithKey merge -- DMap.mergeWithKey merge
                -- (DMap.map ( :^: defQ)) (DMap.map (defP :^: )) mapP mapQ
      where merge _ p q = Just (p :^: q)

instance GEq (K Int) where
    geq (K i) (K j) = if i == j then Just (unsafeCoerce Refl) else Nothing

instance GCompare (K Int) where
    gcompare (K i) (K j) =
      case compare i j of
              LT -> GLT
              EQ -> unsafeCoerce (GEQ :: GOrdering () ())
              GT -> GGT
