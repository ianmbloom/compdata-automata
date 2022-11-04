{-# LANGUAGE TemplateHaskell
  , FlexibleContexts
  , MultiParamTypeClasses
  , RankNTypes
  , TypeOperators
  , FlexibleInstances
  , UndecidableInstances
  , ScopedTypeVariables
  , TypeSynonymInstances
  , GeneralizedNewtypeDeriving
  , IncoherentInstances
  , ConstraintKinds
  , KindSignatures
  , DeriveAnyClass
#-}
module Main where

import Data.Comp.Multi.Automata
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Show
import Data.Comp.Multi hiding (height)
import Data.Foldable
import Prelude hiding (foldl)

import Data.Set (Set, union, singleton, delete, member)
import qualified Data.Set as Set

import Data.Map (Map, (!))
import qualified Data.Map as Map

type Name = String
type NameEnv = Map Name Addr
type Var = String

newtype AddrCount = AddrCount {unAddrCount :: Int} deriving (Eq, Ord, Show, Num)
newtype Addr = Addr {unAddr :: Int} deriving (Eq, Ord, Show, Num)

data Branch a i = Branch (a i) (a i)

data Leaf (a :: * -> *) i = Leaf Name | EmptyLeaf

data Pointer (a :: * -> *) i = Pointer Addr | Null

type Core   = Branch :+: Leaf
type Stored = Branch :+: Pointer

data Let a i = Let Var (a i) (a i)
             | Var Var

type CoreLet   = Let :+: Core
type StoredLet = Let :+: Core

$(derive [makeHFunctor, makeHFoldable, makeHTraversable, smartConstructors, makeShowHF]
  [''Branch, ''Leaf, ''Pointer, ''Let])

class HFoldable f => SizeSt f where
  sizeSt :: UpState f Int

instance SizeSt Leaf where
  sizeSt (Leaf s) = K 1
  sizeSt EmptyLeaf = K 0

instance HFoldable f => SizeSt f where
  sizeSt t = hfoldl (\(K a) (K b) -> K $ a + b) (K 0) t

class AddrSt f q where
  addrSt :: DDownState f q Addr

instance (AddrSt f q, AddrSt g q) => AddrSt (f :+: g) q where
    addrSt (Inl x) = addrSt x
    addrSt (Inr x) = addrSt x

instance (AddrCount :< q, Int :< q) => AddrSt Branch q where
    addrSt (Branch a b) =
      let offset = above
      in K $  a |-> offset
            & b |-> (offset + Addr (below a))

instance (AddrCount :< q, Int :< q) => AddrSt Let q where
    addrSt (Let _ a b) =
      let offset = above
      in K $
           a |-> offset
         & b |-> (offset + Addr (below a))
    addrSt _ = K empty

instance {-# OVERLAPPABLE #-} AddrSt f q where
    addrSt _ = K empty


class StoreLeaf f q where
  storeLeaf :: DUpState f q NameEnv

instance (Addr :< q) => StoreLeaf Leaf q where
  storeLeaf t =
    case t of
      Leaf name -> K $ name `Map.singleton` above
      _ -> K $ Map.empty

instance StoreLeaf Branch q where
  storeLeaf t =
    case t of
      Branch a b -> K $ below a `Map.union` below b

instance {-# OVERLAPPABLE #-} StoreLeaf f q where
  storeLeaf t = K $ Map.empty

class RewriteLeaf f q g where
  rewriteLeaf :: QHom f q g

instance (HFunctor g, RewriteLeaf f q g, RewriteLeaf z q g) => RewriteLeaf (f :+: z) q g where
  rewriteLeaf t =
    case t of
      Inl x -> rewriteLeaf x
      Inr x -> rewriteLeaf x

instance (HFunctor g, Addr :< q, Pointer :<: g) => RewriteLeaf Leaf q g where
  rewriteLeaf t =
    case t of
      Leaf name -> liftCxt $ Pointer above
      EmptyLeaf -> liftCxt   Null

instance (HFunctor g, Branch :<: g) => RewriteLeaf Branch q g where
  rewriteLeaf = liftCxt

class RestoreLeaf f g where
  restoreLeaf :: Map Addr Name -> Hom f g

instance (Leaf :<: g) => RestoreLeaf Pointer g where
  restoreLeaf m t =
    case t of
      Pointer i -> inject (Leaf (m ! i))
      Null -> inject EmptyLeaf

instance {-# OVERLAPPABLE #-} (HFunctor g, f :<: g) => RestoreLeaf f g where
  restoreLeaf m = liftCxt

store :: ( Leaf :<: f
         , Pointer :<: g
         , HTraversable f
         , HFunctor g
         , RewriteLeaf f ((Int, NameEnv), Addr) g
         , StoreLeaf f ((Int, NameEnv), Addr) )
      => Term f i -> ((Int,NameEnv), Term g i)
store = runQHom (dUpState sizeSt `prodDUpState` storeLeaf) (addrSt) rewriteLeaf (Addr 0)

exTree :: Term Core ()
exTree = iBranch (iBranch iEmptyLeaf    (iLeaf "bird"))
                 (iBranch (iLeaf "dog") (iLeaf "cat" ))

main :: IO ()
main = do
  let (i, term) = store exTree :: ((Int, NameEnv), Term Stored ())
  putStrLn . show $ term
  putStrLn . show $ i
