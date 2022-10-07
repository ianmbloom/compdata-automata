{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Automata
-- Copyright   :  (c) 2010-2012 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines stateful term homomorphisms. This (slightly
-- oxymoronic) notion extends per se stateless term homomorphisms with
-- a state that is maintained separately by a bottom-up or top-down
-- state transformation. Additionally, this module also provides
-- combinators to run state transformations themselves.
--
-- Like regular term homomorphisms also stateful homomorphisms (as
-- well as transducers) can be lifted to annotated signatures
-- (cf. "Data.Comp.Annotation").
--
-- The recursion schemes provided in this module are derived from tree
-- automata. They allow for a higher degree of modularity and make it
-- possible to apply fusion. The implementation is based on the paper
-- /Modular Tree Automata/ (Mathematics of Program Construction,
-- 263-299, 2012, <http://dx.doi.org/10.1007/978-3-642-31113-0_14>).
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Automata
    (
    -- * Stateful Term Homomorphisms
      QHom
    , below
    , above
    , pureHom
    -- ** Bottom-Up State Propagation
    , upTrans
    , runUpHom
    , runUpHomSt
    -- ** Top-Down State Propagation
    , downTrans
    , runDownHom
    -- ** Bidirectional State Propagation
    , runQHom
    -- * Deterministic Bottom-Up Tree Transducers
    , UpTrans
    , UpTrans'
    , mkUpTrans
    , runUpTrans
    , compUpTrans
    , compUpTransHom
    , compHomUpTrans
    , compUpTransSig
    , compSigUpTrans
    , compAlgUpTrans
    -- * Deterministic Bottom-Up Tree State Transformations
    -- ** Monolithic State
    , UpState
    , tagUpState
    , runUpState
    , prodUpState
    -- ** Modular State
    , DUpState
    , dUpState
    , upState
    , runDUpState
    , prodDUpState
    , (|*|)
    -- * Deterministic Top-Down Tree Transducers
    , DownTrans
    , DownTrans'
    , mkDownTrans
    , runDownTrans
    , compDownTrans
    , compDownTransSig
    , compSigDownTrans
    , compDownTransHom
    , compHomDownTrans
    -- * Deterministic Top-Down Tree State Transformations
    -- ** Monolithic State
    , DownState
    , tagDownState
    , prodDownState
    -- ** Modular State
    , DDownState
    , dDownState
    , downState
    , prodDDownState
    , (>*<)
    -- * Bidirectional Tree State Transformations
    , runDState
    -- * Operators for Finite Mappings
    , (&)
    , (|->)
    , empty
    -- * Product State Spaces
    , module Data.Projection
    -- * Annotations
    , propAnnQ
    , propAnnUp
    , propAnnDown
    , pathAnn
    ) where

-- import Data.Functor.Compose
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Comp.Multi.DMapping
import Data.Comp.Multi.Term
import Data.Comp.Multi.Ops
import qualified Data.Comp.Ops as O
import Data.Projection.Multi
import Data.Functor.Compose

-- | This function provides access to components of the states from
-- "below".

below :: forall p q a i . (?below :: a i -> q i, p :<< q) => a i -> p i
below = pr . ?below

-- | This function provides access to components of the state from
-- "above"

above :: forall p q i . (?above :: q i, p :<< q) => p i
above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.

explicit :: forall q a b (i :: *) . ((?above :: q i , ?below :: a i -> q i) => b i) -> q i -> (a i -> q i) -> b i
explicit x ab be = x where ?above = ab; ?below = be

fexplicit :: forall f g q a qa i
          .  (f a :->: g a) i
          -> q i
          -> (a i -> q i)
          -> (f a :->: g a) i
fexplicit x ab be = x where ?above = ab; ?below = be

-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a bottom-up or top-down state transformation function (or both).

type QHom (f :: (* -> *) -> * -> *) q g = forall a i . (?below :: a i -> q i, ?above :: q i) => (f a :->: Context g a) i


-- | This function turns a stateful homomorphism with a fully
-- polymorphic state type into a (stateless) homomorphism.
pureHom :: (forall q . QHom f q g) -> Hom f g
pureHom (HFun phom) t =
  let ?above = undefined
      ?below = const undefined
  in phom t

-- | This type represents transition functions of total, deterministic
-- bottom-up tree transducers (UTTs).

type UpTrans f q g = forall a . f (q :^: a) :-> (q :^: Context g a)


-- | This is a variant of the 'UpTrans' type that makes it easier to
-- define UTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type UpTrans' f q g = forall a i. (f (q :^: Context g a) :->: (q :^: Context g a)) i

-- | This function turns a UTT defined using the type 'UpTrans'' in
-- to the canonical form of type 'UpTrans'.

mkUpTrans :: HFunctor f => UpTrans' f q g -> UpTrans f q g
mkUpTrans (HFun tr) = \ t -> tr $ hfmap (\(q :^: a) -> (q :^: Hole a)) t

-- | This function transforms a UTT transition function into an
-- algebra.

upAlg :: (HFunctor g)  => UpTrans f q g -> Alg f (q :^: Term g)
upAlg trans = hfmap appCxt . trans

-- | This function runs the given UTT on the given term.

runUpTrans :: (HFunctor f, HFunctor g) => UpTrans f q g -> Term f :-> Term g
runUpTrans trans = hsnd . runUpTransSt trans

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runUpTransSt :: (HFunctor f, HFunctor g) => UpTrans f q g -> Term f :-> (q :^: Term g)
runUpTransSt up t = cata (upAlg up) t

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.

runUpTrans' :: forall f g q a . (HFunctor f, HFunctor g) => UpTrans f q g -> Context f (q :^: a) :-> (q :^: Context g a)
runUpTrans' trans = run where
    run :: Context f (q :^: a) :-> (q :^: Context g a)
    run (Hole (q :^: a)) = q :^: Hole a
    run (Term t) = hfmap appCxt $ trans $ hfmap run t

-- | This function composes two UTTs. (see TATA, Theorem 6.4.5)

compUpTrans :: (HFunctor f, HFunctor g, HFunctor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q :^:p) h
compUpTrans t2 t1 x = ((q1 :^: q2) :^: c2) where
    (q1 :^: c1) = t1 $ hfmap (\((q1 :^: q2) :^: a) -> (q1 :^: (q2 :^: a))) x
    (q2 :^: c2) = runUpTrans' t2 c1


-- | This function composes a UTT with an algebra.

compAlgUpTrans :: (HFunctor g)
               => Alg g a -> UpTrans f q g -> Alg f (q :^:a)
compAlgUpTrans alg trans = hfmap (cata' alg) . trans


-- | This combinator composes a UTT followed by a signature function.

compSigUpTrans :: (HFunctor g) => SigFun g h -> UpTrans f q g -> UpTrans f q h
compSigUpTrans sig trans x = (q :^: appSigFun sig x') where
    (q :^: x') = trans x

-- | This combinator composes a signature function followed by a UTT.

compUpTransSig :: UpTrans g q h -> SigFun f g -> UpTrans f q h
compUpTransSig trans sig = trans . sig

-- | This combinator composes a UTT followed by a homomorphism.

compHomUpTrans :: (HFunctor g, HFunctor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hom trans x = (q :^: appHom hom x') where
    (q :^: x') = trans x

-- | This combinator composes a homomorphism followed by a UTT.

compUpTransHom :: (HFunctor g, HFunctor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hom x  = runUpTrans' trans . hom $ x

-- | This type represents transition functions of total, deterministic
-- bottom-up tree acceptors (UTAs).

type UpState (f :: (* -> *) -> * -> *) q = Alg f q

-- | Changes the state space of the UTA using the given isomorphism.

tagUpState :: (HFunctor f) =>  (q :-> p) -> (p :-> q) -> UpState f q -> UpState f p
tagUpState i o s = i . s . hfmap o

-- | This combinator runs the given UTA on a term returning the final
-- state of the run.

runUpState :: (HFunctor f) => UpState f q -> Term f :-> q
runUpState = cata

-- | This function combines the product UTA of the two given UTAs.

prodUpState :: HFunctor f => UpState f p -> UpState f q -> UpState f (p :^: q)
prodUpState sp sq t = (p :^: q) where
    p = sp $ hfmap hfst t
    q = sq $ hfmap hsnd t

-- | This function constructs a UTT from a given stateful term
-- homomorphism with the state propagated by the given UTA.

appHFun (HFun f) t = f t
upTrans :: forall f g q . (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = (q :^: c)
    where
          q = st $ hfmap hfst t
          c = hfmap hsnd $ appHFun (fexplicit f q hfst) t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given UTA to a term.

runUpHom :: (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> Term f :-> Term g
runUpHom st hom = hsnd . runUpHomSt st hom

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.

runUpHomSt :: (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> Term f :-> (q :^:Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GUTAs) which have access
-- to an extended state space.

type DUpState (f :: (* -> *) -> * -> *) p q = (q :<< p) => DUpState' f p q
type DUpState' f p q = forall a i j . (?below :: a i -> p i, ?above :: p i) => (f a :->: q) i

-- | This combinator turns an arbitrary UTA into a GUTA.

dUpState :: HFunctor f => UpState f q -> DUpState f p q
dUpState f = HFun $ f . hfmap below

-- | This combinator turns a GUTA with the smallest possible state
-- space into a UTA.

upState :: DUpState f q q -> UpState f q
upState f s = res where res = appHFun (explicit f res id) s

-- | This combinator runs a GUTA on a term.

runDUpState :: HFunctor f => DUpState f q q -> Term f :-> q
runDUpState up t = runUpState (upState up) t

-- | This combinator constructs the product of two GUTA.

prodDUpState :: (p :<< c, q :<< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p :^: q)
prodDUpState sp sq = HFun $ \ t -> (appHFun sp t :^: appHFun sq t)

(|*|) :: (p :<< c, q :<< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p :^: q)
(|*|) = prodDUpState


data (a :->: b) i = HFun {unHFun :: a i -> b i}

hcomp :: (b :->: c) i -> (a :->: b) i -> (a :->: c) i
hcomp (HFun f) (HFun g) = HFun (f . g)

hcurry :: ((q :^: p) :->: a) i -> (q :->: (p :->: a)) i
hcurry (HFun f) = HFun (\a -> HFun (\b -> f (a :^: b)))

huncurry :: (a :->: (b :->: c)) i -> ((a :^: b) :->: c) i
huncurry (HFun f) = HFun $ \ (a :^: b) -> (unHFun $ f a) b

-- | This type represents transition functions of total deterministic
-- top-down tree transducers (DTTs).

type DownTrans f q g = forall a i . q i -> f (q :->: a) i -> Context g a i

-- | This is a variant of the 'DownTrans' type that makes it easier to
-- define DTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type DownTrans' f q g = forall a i . q i -> f (q :->: Context g a) i -> Context g a i

-- | This function turns a DTT defined using the type 'DownTrans'' in
-- to the canonical form of type 'DownTrans'.
mkDownTrans :: HFunctor f => DownTrans' f q g -> DownTrans f q g
mkDownTrans trans q t = trans q (hfmap (HFun Hole `hcomp`) t)

-- | Thsis function runs the given DTT on the given tree.

runDownTrans :: forall h f g q a . (HFunctor f, HFunctor g) => DownTrans f q g -> forall i . q i -> Cxt h f a i -> Cxt h g a i
runDownTrans trans q t = run t q where
    run :: forall j . Cxt h f a j -> q j -> Cxt h g a j
    run (Term t) q = appCxt $ trans q $ hfmap (hpartial run) t
    run (Hole a) _ = Hole a

-- | This function runs the given DTT on the given tree.

hpartial :: (a i -> b i -> c i) -> a i -> (b :->: c) i
hpartial f a = HFun (f a)

runDownTrans' :: forall h f g q a . (HFunctor f, HFunctor g) => DownTrans f q g -> forall i . q i -> Cxt h f (q :->: a) i -> Cxt h g a i
runDownTrans' trans q t = run t q where
    run :: forall j . Cxt h f (q :->: a) j -> q j -> Cxt h g a j
    run (Term t) q = appCxt $ trans q $ hfmap (hpartial run) t
    run (Hole (HFun a)) q = Hole (a q)

-- | This function composes two DTTs. (see W.C. Rounds /Mappings and
-- grammars on trees/, Theorem 2.)

compDownTrans :: (HFunctor f, HFunctor g, HFunctor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q :^: p) h
compDownTrans t2 t1 (q :^: p) t = runDownTrans' t2  p $ t1 q (hfmap hcurry t)



-- | This function composes a signature function after a DTT.

compSigDownTrans :: (HFunctor g) => SigFun g h -> DownTrans f q g -> DownTrans f q h
compSigDownTrans sig trans q = appSigFun sig . trans q

-- | This function composes a DTT after a function.

compDownTransSig :: DownTrans g q h -> SigFun f g -> DownTrans f q h
compDownTransSig trans hom q t = trans q (hom t)


-- | This function composes a homomorphism after a DTT.

compHomDownTrans :: (HFunctor g, HFunctor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hom trans q = appHom hom . trans q

-- | This function composes a DTT after a homomorphism.

compDownTransHom :: (HFunctor g, HFunctor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hom q t = runDownTrans' trans q (hom t)


-- | This type represents transition functions of total, deterministic
-- top-down tree acceptors (DTAs).

type DownState (f :: (* -> *) -> * -> *) (q :: * -> *) = forall (m :: (* -> *) -> *) (a :: * -> *) i . DMapping m a => (q :^: f a) i -> m q

-- | Changes the state space of the DTA using the given isomorphism.

tagDownState :: (q :-> p) -> (p :-> q) -> DownState f q -> DownState f p
tagDownState i o t (q :^: s) = fmap i $ t (o q :^: s)

-- | This function constructs the product DTA of the given two DTAs.

prodDownState :: DownState f p -> DownState f q -> DownState f (p :^: q)
prodDownState sp sq ((p :^: q) :^: t) = prodMap p q (unK $ sp (p :^: t)) (unK $ sq (q :^: t))


-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.

appMap :: forall f q b i . HTraversable f
       => (forall m k . DMapping m k => (f k :->: K (m q)) i)
       -> q i -> f (q :->: b) i -> f (q :^: b) i
appMap qmap q s =
    let s' :: f (DNumbered (q :->: b)) i
        s' = dNumber s
        qfun :: forall c . DNumbered (q :->: c) i -> (q :^: c) i
        qfun (DNumbered index (HFun a)) =
          let q' = lookupDNumMap q index (unK $ appHFun qmap s')
          in  (q' :^: a q')
    in  hfmap qfun s'

-- | This function constructs a DTT from a given stateful term--
-- homomorphism with the state propagated by the given DTA.

downTrans :: (HTraversable f, HFunctor g) => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f q s = hfmap hsnd $ appHFun (fexplicit f q hfst) (appMap (appHFun (hcurry st) q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DTA to a term.

runDownHom :: (HTraversable f, HFunctor g)
            => DownState f q -> QHom f q g -> forall i . q i -> Term f i -> Term g i
runDownHom st h = runDownTrans (downTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDTAs) which have access

-- to an extended state space.
type DDownState f p q = (q :<< p) => DDownState' f p q

type DDownState' f p q = forall m k i . (DMapping m k, ?below :: k i -> p i, ?above :: p i)
                       => (f k :->: K (m q)) i

-- | This combinator turns an arbitrary DTA into a GDTA.

dDownState :: DownState f q -> DDownState f p q
dDownState (HFun f) = HFun $ \t -> f (above :^: t)

-- | This combinator turns a GDTA with the smallest possible state
-- space into a DTA.

downState :: DDownState f q q -> DownState f q
downState f = HFun $
  \ (q :^: s) ->
      let res = appHFun (explicit f q bel) s
          bel k = findWithDefault q k res
      in  res


-- | This combinator constructs the product of two dependant top-down
-- state transformations.

prodDDownState :: (p :<< c, q :<< c)
               => DDownState f c p -> DDownState f c q -> DDownState f c (p :^: q)
prodDDownState sp sq = HFun $ \t -> getCompose $ prodMap (\k -> above) (\k -> above) (appHFun sp t) (appHFun sq t)

-- | This is a synonym for 'prodDDownState'.

(>*<) :: (p :<< c, q :<< c, HFunctor f)
         => DDownState f c p -> DDownState f c q -> DDownState f c (p :^: q)
(>*<) = prodDDownState


-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.

runDState :: forall f u d i . HTraversable f => DUpState' f (u :^: d) u -> DDownState' f (u :^: d) d -> d i -> Term f i -> u i
runDState up down d (Term t) = u where
        t' :: f (DNumbered (u :^: d)) i
        t' = hfmap bel $ dNumber t
        bel :: forall j . DNumbered (Term f) j -> DNumbered (u :^: d) j
        bel (DNumbered index s) =
            let d' :: d j
                d' = lookupDNumMap d index m
            in DNumbered index (runDState up down d' s :^: d')
        m :: f0 (d i)
        m = unK $ appHFun (explicit down (u :^: d) unDNumbered) t'
        u :: u i
        u = appHFun (explicit up (u :^: d) unDNumbered) t'

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runQHom :: forall f g u d i . (HTraversable f, HFunctor g) =>
           DUpState' f (u :^: d) u -> DDownState' f (u :^: d) d ->
           QHom f (u :^: d) g ->
           d i -> Term f i-> (u :^: Term g) i
runQHom up down trans d (Term t) = (u :^: t'') where
        t' :: f (DNumbered ((u :^: d) :^: Term g)) i
        t' = hfmap bel $ dNumber t
        bel :: forall j . DNumbered (Term f) j -> DNumbered ((u :^: d) :^: Term g) j
        bel (DNumbered index s) =
            let d' :: d j
                d' = lookupDNumMap d index m
                (u' :^: s') = runQHom up down trans d' s
            in DNumbered index ((u' :^: d') :^: s')
        m :: f0 (d i)
        m = unK $ appHFun (explicit down (u :^: d) (hfst . unDNumbered)) t'
        u :: u i
        u = appHFun (explicit up (u :^: d) (hfst . unDNumbered)) t'
        t'' = appCxt $ hfmap (hsnd . unDNumbered) $ appHFun (fexplicit trans (u :^: d) (hfst . unDNumbered)) t'


-- | Lift a stateful term homomorphism over signatures @f@ and @g@ to
-- a stateful term homomorphism over the same signatures, but extended with
-- annotations.
propAnnQ :: (DistAnn f p f', DistAnn g p g', HFunctor g)
        => QHom f q g -> QHom f' q g'
propAnnQ hom = HFun $ \ f' ->
    let ((O.:&:) f p) = projectA f'
    in  ann p (appHFun hom f)

-- | Lift a bottom-up tree transducer over signatures @f@ and @g@ to a
-- bottom-up tree transducer over the same signatures, but extended
-- with annotations.
propAnnUp :: (DistAnn f p f', DistAnn g p g', HFunctor g)
        => UpTrans f q g -> UpTrans f' q g'
propAnnUp trans f' = (q :^: ann p t)
    where ((O.:&:) f p) = projectA f'
          (q :^: t) = trans f

-- | Lift a top-down tree transducer over signatures @f@ and @g@ to a
-- top-down tree transducer over the same signatures, but extended
-- with annotations.
propAnnDown :: (DistAnn f p f', DistAnn g p g', HFunctor g)
        => DownTrans f q g -> DownTrans f' q g'
propAnnDown trans q f' = ann p (trans q f)
    where ((O.:&:) f p) = projectA f'


-- | This function adds unique annotations to a term/context. Each
-- node in the term/context is annotated with its path from the root,
-- which is represented as an integer list. It is implemented as a
-- DTT.
pathAnn :: forall g. (HTraversable g) => CxtFun g (g :&: [Int])
pathAnn = runDownTrans trans (K []) where
    trans :: DownTrans g (K [Int]) (g :&: [Int])
    trans (K q) t = simpCxt (hfmap (\ (DNumbered (K n) (HFun s)) -> s (K (n:q))) (dNumber t) :&: q)
