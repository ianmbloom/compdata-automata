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
module Reduce where

import Control.Monad.State
import Data.Comp.Multi
import Data.Comp.Multi.Automata
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Derive
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Show

import Data.Map (Map, (!))
import qualified Data.Map as M

import Debug.Trace

class UnTouchAnn f v g where
  unTouch :: Proxy v -> SigFun f g

instance (UnTouchAnn f v z, UnTouchAnn g v z) => UnTouchAnn (f :+: g) v z where
  unTouch p t = case t of
    Inl x -> unTouch p x
    Inr x -> unTouch p x

instance {-# OVERLAPPABLE #-} (f :<: g) => UnTouchAnn f v g where
  unTouch p t = inj $ t

type Var = String
type Bindings v = Map Var (Touched, Maybe v)
type Touched = Bool


class CheckReducable (f :: (* -> *) -> * -> *) where
  done :: UpState f Bool

instance (CheckReducable f, CheckReducable g) => CheckReducable (f :+: g) where
  done = caseH done done

instance {-# OVERLAPPABLE #-} HFoldable f => CheckReducable f where
  done t = trK "done f" $ hfoldl (\(K a) (K b) -> K $ a && b) (K True) t

class CanBind (f :: (* -> *) -> * -> *) v where
  downBind :: DownState f (Bindings v)

class CanEval (f :: (* -> *) -> * -> *) v where
  upEval :: UpState f (Maybe v)

instance (CanBind f v, CanBind g v) => CanBind (f :+: g) v where
  downBind (q :*: t) =
    case t of
      Inl x -> downBind (q :*: x)
      Inr x -> downBind (q :*: x)

instance (CanEval f v, CanEval g v) => CanEval (f :+: g) v where
  upEval = caseH upEval upEval

instance {-# OVERLAPPABLE #-} HFoldable f => CanBind f v where
  -- Distribute bindings to subterms untouched
  downBind (q :*: t) = K $ hfoldl (\binds k -> binds & (k |-> unK q)) empty t

instance {-# OVERLAPPABLE #-} CanEval f v where
  -- Nonspecific terms are touched and return nothing.
  upEval t = K Nothing

class CanBind f v => CanReduce (f :: (* -> *) -> * -> *) v z where
  subst :: QHom f (Bindings v) z
  touch :: QHom f (Touched, Maybe v) z

instance (CanReduce f v z, CanReduce g v z) => CanReduce (f :+: g) v z where
  subst abv bel = caseH (subst abv bel) (subst abv bel)
  touch abv bel = caseH (touch abv bel) (touch abv bel)

instance {-# OVERLAPPABLE #-} (CanBind f v, HFunctor z, f :<: z) => CanReduce f v z where
  subst abv bel t = liftCxt t
  touch abv bel t = liftCxt t

trWith f m x = trace (m++" "++f x) x

tr :: (Show a) => String -> a -> a
tr = trWith show

trK :: (Show a) => String -> K a i -> K a i
trK = trWith (show . unK)

reduce :: forall v f z i
       . ( HFunctor f
         , HTraversable z
        , UnTouchAnn f v z
        , CheckReducable z
        , CanBind z v
        , CanEval z v
        , CanReduce z v z
        , ShowHF z
        , Show v
        --, f :<: CoreLetTouched
         ) => Proxy v -> Proxy z -> Term f i -> Term z i
reduce p z term = go 5 annTerm
  where
    annTerm :: Term z i
    annTerm = tr "annTerm" $ appSigFun (unTouch p) term
    go :: Int -> Term z i -> Term z i
    go i term =
        let isDone = unK $ runUpState done term
        in  if i < 0 || tr "isDone" isDone
            then term
            else go (i - 1) (runDownHom downBind
                                (subst @z @v @z)
                                M.empty
                                (runUpHom (upState ((dUpState done) `prodDUpState` (dUpState upEval))) (touch @z @v @z) $ tr ("term " ++ show i) term)
                            )
------------------------------------------------------

data Let a i = Let Var (a i) (a i)
             | Var Var

$(derive [makeHFunctor, makeHFoldable, makeHTraversable, smartConstructors, makeShowHF]
  [''Let])

instance (Let :&: (Touched, Maybe v) :<: g) => UnTouchAnn Let v g where
  unTouch p t = inj $ t :&: (False, Nothing :: Maybe v)

instance {-# OVERLAPPING #-} CheckReducable (Let :&: (Touched, Maybe v)) where
  done (t :&: (touched, _)) = trK "done let" $ hfoldl (\(K a) (K b) -> K $ a && b) (K touched) t

instance {-# OVERLAPPING #-} CanBind (Let :&: (Touched, Maybe v)) v where
  downBind (q :*: (t :&: (touched, mVal))) =
    case t of
      Var tag -> K empty
      Let tag subst body ->
        K $ body |-> M.insert tag (touched, mVal) (unK q)

instance {-# OVERLAPPING #-} CanEval (Let :&: (Touched, Maybe v)) v where
  upEval (t :&: (touched, mVal)) =
    case t of
      Var tag -> K mVal
      Let tag _ body -> body


instance {-# OVERLAPPING #-} (HFunctor z, (Let :&: (Touched, Maybe v)) :<: z) => CanReduce (Let :&: (Touched, Maybe v)) v z where
  subst abv bel (t :&: (touched, mVal)) =
    case t of
      Var tag ->
         let ann = if touched
                   then (touched, mVal)
                   else case M.lookup tag abv of
                           Nothing  -> error $ "free var " ++ tag
                           Just new -> new
         in liftCxt (t :&: ann)
      Let tag subst body ->
        case (touched, mVal) of
          (True, Just val) -> Hole body
          _ -> liftCxt $ Let tag subst body :&: (touched, mVal)
  touch abv bel (t :&: (touched, mVal)) =
    case t of
      Var tag -> liftCxt $ Var tag :&: (touched, mVal)
      Let tag subst body -> liftCxt $ Let tag subst body :&: bel subst
