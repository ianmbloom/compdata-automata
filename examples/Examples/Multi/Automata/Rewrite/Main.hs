{-# LANGUAGE TemplateHaskell
  , FlexibleContexts
  , MultiParamTypeClasses
  , RankNTypes
  , TypeOperators
  , TypeApplications
  , FlexibleInstances
  , UndecidableInstances
  , ScopedTypeVariables
  , TypeSynonymInstances
  , GeneralizedNewtypeDeriving
  , IncoherentInstances
  , MonoLocalBinds
  , ConstraintKinds
  , KindSignatures
  #-}

{-#  OPTIONS_GHC -ddump-splices #-}
module Main where

import Control.Monad.State
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
import qualified Data.Map as M

import Reduce

import Debug.Trace

type Name = String
type NameEnv = Map Name Addr

newtype AddrCount = AddrCount {unAddrCount :: Int} deriving (Eq, Ord, Show, Num)
newtype Addr = Addr {unAddr :: Int} deriving (Eq, Ord, Show, Num)

data Branch a i = Branch (a i) (a i)

data Leaf (a :: * -> *) i = Leaf Name

data Null (a :: * -> *) i = Null

data Pointer (a :: * -> *) i = Pointer Addr

type Core   = Branch :+: Leaf :+: Null
type CoreAnn = Branch :+: (Leaf :&: Addr) :+: Null
type Stored = Branch :+: Pointer :+: Null


type CoreLet   = Let :+: Core
type StoredLet = Let :+: Core

$(derive [makeHFunctor, makeHFoldable, makeHTraversable, smartConstructors, makeShowHF]
  [''Branch, ''Leaf, ''Pointer, ''Null])

class HFoldable f => SizeSt f where
  sizeSt :: UpState f Int

instance SizeSt Leaf where
  sizeSt (Leaf s) = K 1

instance HFoldable f => SizeSt f where
  sizeSt t = hfoldl (\(K a) (K b) -> K $ a + b) (K 0) t

class AddrSt f q where
  addrSt :: DDownState f q Addr

instance (AddrSt f q, AddrSt g q) => AddrSt (f :+: g) q where
    addrSt abv bel (Inl x) = addrSt abv bel x
    addrSt abv bel (Inr x) = addrSt abv bel x

instance (AddrCount :< q, Int :< q) => AddrSt Branch q where
    addrSt abv bel (Branch a b) =
      let offset = pr abv
      in K $  a |-> offset
            & b |-> (offset + Addr (pr $ bel a))

instance (AddrCount :< q, Int :< q) => AddrSt Let q where
    addrSt abv bel (Let _ a b) =
      let offset = pr abv
      in K $
           a |-> offset
         & b |-> (offset + Addr (pr $ bel a))
    addrSt abv bel _ = K empty

instance {-# OVERLAPPABLE #-} AddrSt f q where
    addrSt abv bel _ = K empty

class NumLeaf f g where
  numLeaf :: SigFunM (State Addr) f g

--type NatM m f g = forall i. f i -> m (g i)

instance ((Leaf :&: Addr) :<: g) => NumLeaf Leaf g where
  numLeaf (Leaf name) =
    do i <- get
       put (i+1)
       return $ inj (Leaf name :&: i)

instance (NumLeaf f g, NumLeaf z g) => NumLeaf (f :+: z) g where
  numLeaf t =
    case t of
      Inl x -> numLeaf x
      Inr x -> numLeaf x

instance {-# OVERLAPPABLE #-} (f :<: g) => NumLeaf f g where
  numLeaf = return . inj

class StoreLeaf f where
  storeLeaf :: Alg f (K NameEnv)

instance (StoreLeaf f, StoreLeaf g) => StoreLeaf (f :+: g) where
  storeLeaf t =
    case t of
      Inl x -> storeLeaf x
      Inr x -> storeLeaf x

instance StoreLeaf (Leaf :&: Addr) where
  storeLeaf t =
    case t of
      (Leaf name :&: addr) -> K $ name `M.singleton` addr

instance StoreLeaf Branch where
  storeLeaf t =
    case t of
      Branch (K a) (K b) -> K $ a `M.union` b

instance {-# OVERLAPPABLE #-} StoreLeaf f where
  storeLeaf _ = K $ M.empty

class RewriteLeaf f g where
  rewriteLeaf :: Hom f g

instance (HFunctor g, RewriteLeaf f g, RewriteLeaf z g) => RewriteLeaf (f :+: z) g where
  rewriteLeaf t =
    case t of
      Inl x -> rewriteLeaf x
      Inr x -> rewriteLeaf x

instance (HFunctor g, Pointer :<: g) => RewriteLeaf (Leaf :&: Addr) g where
  rewriteLeaf t =
    case t of
      (Leaf name :&: addr) -> liftCxt $ Pointer addr

instance (HFunctor g, f :<: g) => RewriteLeaf f g where
  rewriteLeaf = liftCxt

class RestoreLeaf f g where
  restoreLeaf :: Map Addr Name -> Hom f g

instance (Leaf :<: g) => RestoreLeaf Pointer g where
  restoreLeaf m t =
    case t of
      Pointer i -> inject (Leaf (m ! i))

instance (RestoreLeaf f g, RestoreLeaf z g) => RestoreLeaf (f :+: z) g where
  restoreLeaf m t =
    case t of
      Inl x -> restoreLeaf m x
      Inr x -> restoreLeaf m x

instance {-# OVERLAPPABLE #-} (HFunctor g, f :<: g) => RestoreLeaf f g where
  restoreLeaf m = liftCxt

store :: forall i .
         (
         )
      => Term Core i -> (NameEnv, Term CoreAnn i, Term Stored i)
store term =
  let (annTerm :: Term CoreAnn i) = evalState (appSigFunM (numLeaf) term) (Addr 0)
      K leafMap = cata storeLeaf annTerm
      rewrite = appHom (rewriteLeaf) annTerm
  in  (leafMap, annTerm, rewrite)
  -- runQHom (dUpState sizeSt `prodDUpState` storeLeaf) addrSt rewriteLeaf (Addr 0)

-----------------------------------------------------------------

type CoreLetTouched v = (Let :&: (Touched, Maybe v)) :+: Core

instance {-# OVERLAPPING #-} CanEval Leaf Name where
  upEval (Leaf name) = K $ Just name

instance {-# OVERLAPPING #-} CanEval Branch Name where
  upEval (Branch (K a) (K b)) = case (a,b) of
    (Just a',Just b') -> K $ Just $ a' ++ b'
    _ -> K Nothing

-----------------------------------------------------------------

exTree :: Term Core ()
exTree = iBranch (iBranch iNull    (iLeaf "bird"))
                 (iBranch (iLeaf "dog") (iLeaf "cat" ))

exLetTree0 :: Term CoreLet ()
exLetTree0 = iLet "0" (iLeaf "dog") (iVar "0")

exLetTree1 :: Term CoreLet ()
exLetTree1 = iLet "0" (iLeaf "dog") (iLet "1" (iLeaf "cat") (iBranch (iVar "0") (iVar "1")))

exLetTree2 :: Term CoreLet ()
exLetTree2 = iLet "0" (iBranch (iLet "2" (iLeaf "dog") (iVar "2")) (iLeaf "bird"))
                      (iLet "1" (iLeaf "cat") (iBranch (iVar "0") (iVar "1")))

invertBijection :: (Ord k, Ord v) => Map k v -> Map v k
invertBijection = M.foldrWithKey (flip M.insert) M.empty

main :: IO ()
main = do
  -- let (mapping, annTerm, term) = store exTree :: (NameEnv, Term CoreAnn (), Term Stored ())
  -- putStrLn . show $ annTerm
  -- putStrLn . show $ term
  -- putStrLn . show $ mapping
  -- let (restored :: Term Core ()) = appHom (restoreLeaf (invertBijection mapping)) term
  -- putStrLn . show $ restored

  let redTerm = reduce (P :: Proxy Name) (P :: Proxy (CoreLetTouched Name)) exLetTree2
  putStrLn . show $ redTerm
