{-# LANGUAGE TemplateHaskell, FlexibleContexts, MultiParamTypeClasses,
TypeOperators, FlexibleInstances, UndecidableInstances,
ScopedTypeVariables, TypeSynonymInstances, GeneralizedNewtypeDeriving,
OverlappingInstances, ConstraintKinds, KindSignatures, DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}

module Automata.Compiler where

import Data.Comp.Multi.Automata
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Ops
import Data.Comp.Multi hiding (height)
import Data.Foldable
import Prelude hiding (foldl)

import Data.Set (Set, union, singleton, delete, member)
import qualified Data.Set as Set

import Data.Map (Map)
import qualified Data.Map as Map

type Var = String

data Val (a :: * -> *) i = Const Int

data Op a i = Plus  (a i) (a i)
            | Times (a i) (a i)

type Core = Op :+: Val

data Let a i = Let Var (a i) (a i)
             | Var Var
--   deriving HFunctor
type CoreLet = Let :+: Core

data Sugar a i = Neg (a i)
               | Minus (a i) (a i)
-- deriving HFunctor

$(derive [makeHFunctor, makeHFoldable, makeHTraversable, smartConstructors, makeShowHF]
  [''Val, ''Op, ''Let, ''Sugar])


class Eval f where
    evalSt :: UpState f Int

$(derive [liftSum] [''Eval])

instance Eval Val where
    evalSt (Const i) = K i

instance Eval Op where
    evalSt (Plus  x y) = x + y
    evalSt (Times x y) = x * y

type Addr = Int

data Instr = Acc Int
           | Load Addr
           | Store Addr
           | Add Int
           | Sub Int
           | Mul Int
             deriving (Show)

type Code = [Instr]

data MState = MState {
      mRam :: Map Addr Int,
      mAcc :: Int }

runCode :: Code -> MState -> MState
runCode [] = id
runCode (ins:c) = runCode c . step ins
    where step (Acc i) s = s{mAcc = i}
          step (Load a) s = case Map.lookup a (mRam s) of
              Nothing -> error $ "memory cell " ++ show a ++ " is not set"
              Just n -> s {mAcc = n}
          step (Store a) s = s {mRam = Map.insert a (mAcc s) (mRam s)}
          step (Add a) s = exec (+) a s
          step (Sub a) s = exec (-) a s
          step (Mul a) s = exec (*) a s
          exec op a s = case Map.lookup a (mRam s) of
                        Nothing -> error $ "memory cell " ++ show a ++ " is not set"
                        Just n -> s {mAcc = mAcc s `op` n}


runCode' :: Code -> Int
runCode' c = mAcc $ runCode c MState{mRam = Map.empty, mAcc = error "accumulator is not set"}


-- | Defines the height of an expression.
heightSt :: HFoldable f => UpState f Int
heightSt t = hfoldl max 0 t + 1

tmpAddrSt :: HFoldable f => UpState f Int
tmpAddrSt = (+1) . heightSt


newtype VarAddr = VarAddr {varAddr :: Int} deriving (Eq, Show, Num)

class VarAddrSt f where
  varAddrSt :: DownState f VarAddr

instance (VarAddrSt f, VarAddrSt g) => VarAddrSt (f :+: g) where
    varAddrSt (K q :*: Inl x) = varAddrSt (K q :*: x)
    varAddrSt (K q :*: Inr x) = varAddrSt (K q :*: x)

instance VarAddrSt Let where
  varAddrSt (K d :*: Let _ _ x) = K $ x |-> (d + 2)
  varAddrSt _ = K empty

instance VarAddrSt f where
  varAddrSt _ = K empty


type Bind = Map Var Int

bindSt :: (Let :<: f,VarAddr :< q) => DDownState f q Bind
bindSt t = case proj t of
             Just (Let v _ e) -> K $ e |-> q'
                       where q' = Map.insert v (varAddr above) above
             _ -> K empty

-- | Defines the code that an expression is compiled to. It depends on
-- an integer state that denotes the height of the current node.
class CodeSt f q where
    codeSt :: DUpState f q Code

instance (CodeSt f q, CodeSt g q) => CodeSt (f :+: g) q where
    codeSt (Inl x) = codeSt x
    codeSt (Inr x) = codeSt x


instance CodeSt Val q where
    codeSt (Const i) = K [Acc i]

instance (Int :< q) => CodeSt Op q where
    codeSt (Plus x y) = K $ below x ++ [Store i] ++ below y ++ [Add i]
        where i = below y
    codeSt (Times x y) = K $ below x ++ [Store i] ++ below y ++ [Mul i]
        where i = below y

instance (VarAddr :< q, Bind :< q) => CodeSt Let q where
    codeSt (Let _ b e) = K $ below b ++ [Store i] ++ below e
                    where i = varAddr above
    codeSt (Var v) = case Map.lookup v above of
                       Nothing -> error $ "unbound variable " ++ v
                       Just i -> K [Load i]

compile' :: (CodeSt f (Code,Int), HFoldable f, HFunctor f) => Term f i -> (Code, Int)
compile' = unK . runDUpState (codeSt `prodDUpState` dUpState tmpAddrSt)


exComp' = compile' (iConst 2 `iPlus` iConst 3 :: Term Core i)



compile :: (CodeSt f ((Code,Int),(Bind,VarAddr)), HTraversable f, HFunctor f, Let :<: f, VarAddrSt f)
           => Term f i -> Code
compile = fst . runDState
          (codeSt `prodDUpState` dUpState tmpAddrSt)
          (bindSt `prodDDownState` dDownState varAddrSt)
          (Map.empty, VarAddr 1)


exComp = compile (iLet "x" (iLet "x" (iConst 5) (iConst 10 `iPlus` iVar "x")) (iConst 2 `iPlus` iVar "x") :: Term CoreLet ())

-- | Defines the set of free variables
class VarsSt f where
    varsSt :: UpState f (Set Var)

$(derive [liftSum] [''VarsSt])

instance VarsSt Val where
    varsSt _ = K Set.empty

instance VarsSt Op where
    varsSt (Plus (K x) (K y)) = K $ x `union` y
    varsSt (Times (K x) (K y)) = K $ x `union` y

instance VarsSt Let where
    varsSt (Var v) = K $ singleton v
    varsSt (Let v (K x) (K y)) = K $ (if v `member` y then x else Set.empty) `union` delete v y

-- | Stateful homomorphism that removes unnecessary let bindings.
remLetHom :: (Set Var :< q, Let :<: f, HFunctor f) => QHom f q f
remLetHom t = case proj t of
                Just (Let v _ y)
                    | not (v `member` below y) -> Hole y
                _ -> simpCxt t

-- | Removes unnecessary let bindings.
remLet :: (Let :<: f, HFunctor f, VarsSt f) => Term f i -> Term f i
remLet = runUpHom varsSt remLetHom

exLet = remLet (iLet "x" (iConst 3) (iConst 2 `iPlus` iVar "y") :: Term CoreLet ())
