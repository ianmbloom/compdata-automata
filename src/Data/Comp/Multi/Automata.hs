{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE TypeApplications    #-}

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
    --, below
    --, above
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

    , (:->:)(..)
    , (:*:)(..)
    , ffst
    , fsnd
    ) where

import Data.Kind
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.Annotation
import Data.Projection
import Data.Comp.Multi.Mapping
import Data.Comp.Multi.Term
-- import qualified Data.Comp.Multi.DMapping as D
import Data.Comp.Multi.Ops
import qualified Data.Comp.Ops as O

-- Higher order product special cases.

-- | This function provides access to components of the states from
-- "below".

-- below :: forall p q a i . (?below :: a i -> q, p :< q) => a i -> p
-- below = pr . ?below

-- | This function provides access to components of the state from
-- "above"

-- above :: (?above :: q, p :< q) => p
-- above = pr ?above

-- | Turns the explicit parameters @?above@ and @?below@ into explicit
-- ones.

-- explicit :: forall b q a i . ((?above :: q, ?below :: a i -> q) => b i) -> q -> (a i -> q) -> b i
-- explicit x ab be = x where ?above = ab; ?below = be

-- hexplicit :: ((?above::q) => ((forall i . a i -> q) -> f a i -> k i))
--           -> q
--           -> (forall i . a i -> q)
--           -> f a i
--           -> k i
-- hexplicit x ab = x where ?above = ab

-- | This type represents stateful term homomorphisms. Stateful term
-- homomorphisms have access to a state that is provided (separately)
-- by a bottom-up or top-down state transformation function (or both).

type QHom f q g = forall k . q -> (forall i . k i -> q) -> f k :-> Context g k

-- | This function turns a stateful homomorphism with a fully
-- polymorphic state type into a (stateless) homomorphism.
pureHom :: (forall q . QHom f q g) -> Hom f g
pureHom phom t = phom undefined (const undefined) t

-- | This type represents transition functions of total, deterministic
-- bottom-up tree transducers (UTTs).

type UpTrans f q g = forall a . f (K q :*: a) :-> (K q :*: Context g a)

-- | This is a variant of the 'UpTrans' type that makes it easier to
-- define UTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type UpTrans' f q g = forall a . f (K q :*: Context g a) :-> (K q :*: Context g a)

-- | This function turns a UTT defined using the type 'UpTrans'' in
-- to the canonical form of type 'UpTrans'.

mkUpTrans :: HFunctor f => UpTrans' f q g -> UpTrans f q g
mkUpTrans tr t = tr $ hfmap (\(kq :*: a) -> (kq :*: Hole a)) t

-- | This function transforms a UTT transition function into an
-- algebra.

instance HFunctor ((:*:) q) where
  hfmap f (a :*: b) = a :*: f b

upAlg :: (HFunctor g)  => UpTrans f q g -> Alg f (K q :*: Term g)
upAlg trans = hfmap appCxt . trans

-- | This function runs the given UTT on the given term.

runUpTrans :: (HFunctor f, HFunctor g) => UpTrans f q g -> Term f :-> Term g
runUpTrans trans = fsnd . runUpTransSt trans

-- | This function is a variant of 'runUpTrans' that additionally
-- returns the final state of the run.

runUpTransSt :: (HFunctor f, HFunctor g) => UpTrans f q g -> Term f :-> (K q :*: Term g)
runUpTransSt up t = cata (upAlg up) t

-- | This function generalises 'runUpTrans' to contexts. Therefore,
-- additionally, a transition function for the holes is needed.

runUpTrans' :: forall f g q a . (HFunctor f, HFunctor g) => UpTrans f q g -> Context f (K q :*: a) :-> (K q :*: Context g a)
runUpTrans' trans = run where
    run :: Context f (K q :*: a) :-> (K q :*: Context g a)
    run (Hole (q :*: a)) = (q :*: Hole a)
    run (Term t) = hfmap appCxt $ trans $ hfmap run t

-- | This function composes two UTTs. (see TATA, Theorem 6.4.5)

compUpTrans :: (HFunctor f, HFunctor g, HFunctor h)
               => UpTrans g p h -> UpTrans f q g -> UpTrans f (q, p) h
compUpTrans t2 t1 x = (K (q1, q2) :*: c2) where
    (K q1 :*: c1) = t1 $ hfmap (\(K (qa, qb) :*: a) -> (K qa :*: (K qb :*: a))) x
    (K q2 :*: c2) = runUpTrans' t2 c1


-- | This function composes a UTT with an algebra.

compAlgUpTrans :: (HFunctor g)
               => Alg g a -> UpTrans f q g -> Alg f (K q :*: a)
compAlgUpTrans alg trans = hfmap (cata' alg) . trans


-- | This combinator composes a UTT followed by a signature function.

compSigUpTrans :: (HFunctor g) => SigFun g h -> UpTrans f q g -> UpTrans f q h
compSigUpTrans sig trans x = (q :*: appSigFun sig x') where
    (q :*: x') = trans x

-- | This combinator composes a signature function followed by a UTT.

compUpTransSig :: UpTrans g q h -> SigFun f g -> UpTrans f q h
compUpTransSig trans sig = trans . sig

-- | This combinator composes a UTT followed by a homomorphism.

compHomUpTrans :: (HFunctor g, HFunctor h) => Hom g h -> UpTrans f q g -> UpTrans f q h
compHomUpTrans hm trans x = (q :*: appHom hm x') where
    (q :*: x') = trans x

-- | This combinator composes a homomorphism followed by a UTT.

compUpTransHom :: (HFunctor g, HFunctor h) => UpTrans g q h -> Hom f g -> UpTrans f q h
compUpTransHom trans hm x  = runUpTrans' trans . hm $ x

-- | This type represents transition functions of total, deterministic
-- bottom-up tree acceptors (UTAs).

-- type Alg f e = f e :-> e
type UpState f q = Alg f (K q)

-- | Changes the state space of the UTA using the given isomorphism.

tagUpState :: (HFunctor f) => (q -> p) -> (p -> q) -> UpState f q -> UpState f p
tagUpState i o s = K . i . unK . s . hfmap (K . o . unK)

-- | This combinator runs the given UTA on a term returning the final
-- state of the run.

runUpState :: (HFunctor f) => UpState f q -> Term f :-> K q
runUpState = cata

-- | This function combines the product UTA of the two given UTAs.

prodUpState :: HFunctor f => UpState f p -> UpState f q -> UpState f (p, q)
prodUpState sp sq t = K (p, q) where
    K p = sp $ hfmap (K . fst . unK) t
    K q = sq $ hfmap (K . snd . unK) t


-- | This function constructs a UTT from a given stateful term
-- homomorphism with the state propagated by the given UTA.

upTrans :: forall f q g . (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> UpTrans f q g
upTrans st f t = (K q :*: c)
    where K q = st $ hfmap ffst t
          c = hfmap fsnd $ {-hexplicit-} f q (unK . ffst) t

-- | This function applies a given stateful term homomorphism with
-- a state space propagated by the given UTA to a term.

runUpHom :: (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> Term f :-> Term g
runUpHom st hm = fsnd . runUpHomSt st hm

-- | This is a variant of 'runUpHom' that also returns the final state
-- of the run.

runUpHomSt :: (HFunctor f, HFunctor g) => UpState f q -> QHom f q g -> Term f :-> (K q :*: Term g)
runUpHomSt alg h = runUpTransSt (upTrans alg h)


-- | This type represents transition functions of generalised
-- deterministic bottom-up tree acceptors (GUTAs) which have access
-- to an extended state space.

-- type  UpState f q = forall i . f (K q) i -> K q i
type DUpState f p q = (q :< p) => DUpState' f p q
type DUpState' f p q = forall k . p -> (forall i . k i -> p) -> f k :-> K q

-- | This combinator turns an arbitrary UTA into a GUTA.

dUpState :: forall f p q . HFunctor f => UpState f q -> DUpState f p q
dUpState f _abv bel sig = f $ hfmap (K . pr . bel) sig

-- | This combinator turns a GUTA with the smallest possible state
-- space into a UTA.

upState :: forall f q . DUpState f q q -> UpState f q
upState f s = K res where res = unK $ f res unK s

-- | This combinator runs a GUTA on a term.

runDUpState :: HFunctor f => DUpState f q q -> Term f :-> K q
runDUpState up t = runUpState (upState up) t

-- | This combinator constructs the product of two GUTA.

prodDUpState :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p, q)
prodDUpState sp sq abv bel t = K (unK $ sp abv bel t, unK $ sq abv bel t)

(|*|) :: (p :< c, q :< c)
             => DUpState f c p -> DUpState f c q -> DUpState f c (p, q)
(|*|) = prodDUpState



-- | This type represents transition functions of total deterministic
-- top-down tree transducers (DTTs).

data (q :->: a) i = HFun {appHFun :: q i -> a i}

compHFun :: (b :->: c) i -> (a :->: b) i -> (a :->: c) i
compHFun (HFun g) (HFun f) = HFun $ g . f


type DownTrans f q g = forall a i . q -> f (K q :->: a) i -> Context g a i


-- | This is a variant of the 'DownTrans' type that makes it easier to
-- define DTTs as it avoids the explicit use of 'Hole' to inject
-- placeholders into the result.

type DownTrans' f q g = forall a i . q -> f (K q :->: Context g a) i -> Context g a i

-- | This function turns a DTT defined using the type 'DownTrans'' in
-- to the canonical form of type 'DownTrans'.
mkDownTrans :: HFunctor f => DownTrans' f q g -> DownTrans f q g
mkDownTrans tr q t = tr q (hfmap (HFun Hole `compHFun`) t)

-- | Thsis function runs the given DTT on the given tree.

runDownTrans :: forall f g h q a i . (HFunctor f, HFunctor g) => DownTrans f q g -> q -> Cxt h f a i -> Cxt h g a i
runDownTrans tr q t = run t (K q) where
    run :: forall j . Cxt h f a j -> K q j -> Cxt h g a j
    run (Term t) (K q) = appCxt $ tr q $ hfmap (HFun . run) t
    run (Hole a) _     = Hole a

-- | This function runs the given DTT on the given tree.

runDownTrans' :: forall f g h q a i . (HFunctor f, HFunctor g) => DownTrans f q g -> q -> Cxt h f (K q :->: a) i -> Cxt h g a i
runDownTrans' tr q t = run t (K q) where
    run :: forall j .  Cxt h f (K q :->: a) j -> K q j -> Cxt h g a j
    run (Term t) (K q) = appCxt $ tr q $ hfmap (HFun . run) t
    run (Hole a) (K q) = Hole (appHFun a (K q))

-- | This function composes two DTTs. (see W.C. Rounds /Mappings and
-- grammars on trees/, Theorem 2.)

hcurry :: (K (q, p) :->: a) i -> (K q :->: (K p :->: a)) i
hcurry (HFun f) = HFun $ \ (K q) -> HFun $ \ (K p) -> f $ K (q,p)

compDownTrans :: (HFunctor f, HFunctor g, HFunctor h)
              => DownTrans g p h -> DownTrans f q g -> DownTrans f (q, p) h
compDownTrans t2 t1 (q, p) t = runDownTrans' t2  p $ t1 q (hfmap hcurry t)



-- | This function composes a signature function after a DTT.

compSigDownTrans :: (HFunctor g) => SigFun g h -> DownTrans f q g -> DownTrans f q h
compSigDownTrans sig trans q = appSigFun sig . trans q

-- | This function composes a DTT after a function.

compDownTransSig :: DownTrans g q h -> SigFun f g -> DownTrans f q h
compDownTransSig trans hm q t = trans q (hm t)


-- | This function composes a homomorphism after a DTT.

compHomDownTrans :: (HFunctor g, HFunctor h)
              => Hom g h -> DownTrans f q g -> DownTrans f q h
compHomDownTrans hm trans q = appHom hm . trans q

-- | This function composes a DTT after a homomorphism.

compDownTransHom :: (HFunctor g, HFunctor h)
              => DownTrans g q h -> Hom f g -> DownTrans f q h
compDownTransHom trans hm q t = runDownTrans' trans q (hm t)


-- | This type represents transition functions of total, deterministic
-- top-down tree acceptors (DTAs).

type DownState f q = forall m k. (Functor m, Mapping m k) => forall i . (K q :*: f k) i -> K (m q) i

-- | Changes the state space of the DTA using the given isomorphism.

tagDownState :: (q -> p) -> (p -> q) -> DownState f q -> DownState f p
tagDownState fi fo t (K q :*: s) = K $ fmap fi $ unK $ t (K (fo q) :*: s)

-- | This function constructs the product DTA of the given two DTAs.


prodDownState :: DownState f p -> DownState f q -> DownState f (p, q)
prodDownState sp sq (K (p, q) :*: t) = K $ prodMap p q (unK $ sp (K p :*: t)) (unK $ sq (K q :*: t))


-- | Apply the given state mapping to the given functorial value by
-- adding the state to the corresponding index if it is in the map and
-- otherwise adding the provided default state.

appMap :: forall f q b i
       . HTraversable f
       => (forall m k . (Functor m, Mapping m k) => f k i -> K (m q) i)
       -> q
       -> f (K q :->: b) i
       -> f (K q :*: b) i
appMap qmap q s = hfmap (qfun q) s'
    where s' :: f (Numbered (K q :->: b)) i
          s' = number s
          qfun :: forall j . q -> Numbered (K q :->: b) j -> (K q :*: b) j
          qfun q2 (Numbered i a) =
                  let q' = lookupNumMap q2 i (unK $ qmap s')
                  in (K q' :*: appHFun a (K q'))

-- | This function constructs a DTT from a given stateful term--
-- homomorphism with the state propagated by the given DTA.

mcurry :: forall q f (a :: Type -> Type) m i . ((K q :*: f a) i -> K (m q) i) -> q -> f a i -> K (m q) i
mcurry f q t = f (K q :*: t)

downTrans :: (HTraversable f, HFunctor g) => DownState f q -> QHom f q g -> DownTrans f q g
downTrans st f q s = hfmap fsnd $ f q (unK . ffst) (appMap (mcurry st q) q s)


-- | This function applies a given stateful term homomorphism with a
-- state space propagated by the given DTA to a term.

runDownHom :: (HTraversable f, HFunctor g)
            => DownState f q -> QHom f q g -> forall i . q -> Term f i -> Term g i
runDownHom st h = runDownTrans (downTrans st h)

-- | This type represents transition functions of generalised
-- deterministic top-down tree acceptors (GDTAs) which have access

-- to an extended state space.
type DDownState f p q = (q :< p) => DDownState' f p q

type DDownState' f p q = forall m k . (Functor m, Mapping m k)
                                => p -> (forall i . k i -> p) -> f k :-> K (m q)

-- | This combinator turns an arbitrary DTA into a GDTA.

dDownState :: DownState f q -> DDownState f p q
dDownState f abv _bel t = f (K (pr abv) :*: t)

-- | This combinator turns a GDTA with the smallest possible state
-- space into a DTA.

downState :: forall f q . DDownState f q q -> DownState f q
downState f (K q :*: s) = K res
    where (K res) = f q bel s
          bel k = error "downState not implemented." -- findWithDefault q k res


-- | This combinator constructs the product of two dependant top-down
-- state transformations.

prodDDownState :: (p :< c, q :< c)
               => DDownState f c p -> DDownState f c q -> DDownState f c (p, q)
prodDDownState sp sq abv bel t = K $ prodMap (pr abv) (pr abv) (unK $ sp abv bel t) (unK $ sq abv bel t)

-- | This is a synonym for 'prodDDownState'.

(>*<) :: (p :< c, q :< c, HFunctor f)
         => DDownState f c p -> DDownState f c q -> DDownState f c (p, q)
(>*<) = prodDDownState


-- | This combinator combines a bottom-up and a top-down state
-- transformations. Both state transformations can depend mutually
-- recursive on each other.

runDState :: forall f u d i
          . (HTraversable f)
          => DUpState' f (u, d) u
          -> DDownState' f (u, d) d
          -> d -> Term f i -> u
runDState up down d (Term t) = u where
        t' :: f (Numbered (K (u,d))) i
        t' = hfmap bel $ number t
        bel :: forall j . Numbered (Term f) j -> Numbered (K (u, d)) j
        bel (Numbered i s) =
            let d' :: d
                d' = lookupNumMap d i m
            in Numbered i (K (runDState up down d' s, d'))
        m = unK $ down (u, d) (unK . unNumbered) t'
        u = unK $ up   (u, d) (unK . unNumbered) t'

-- | This combinator runs a stateful term homomorphisms with a state
-- space produced both on a bottom-up and a top-down state
-- transformation.

runQHom :: forall f g u d i . (HTraversable f, HFunctor g) =>
           DUpState' f (u,d) u -> DDownState' f (u, d) d ->
           QHom f (u,d) g ->
           d -> Term f i -> (u, Term g i)
runQHom up down trans d (Term t) = (u, t'') where
        t' = hfmap bel $ number t
        bel :: forall j . Numbered (Term f) j -> Numbered (K (u, d) :*: Term g) j
        bel (Numbered i s) =
            let d' = lookupNumMap d i (unK m)
                (u', s') = runQHom up down trans d' s
            in Numbered i (K (u', d') :*: s')
        m =       down (u,d) (unK . ffst . unNumbered) t'
        u = unK $ up   (u,d) (unK . ffst . unNumbered) t'
        t'' = appCxt $ hfmap (fsnd . unNumbered) $ trans (u,d) (unK . ffst . unNumbered) t'

-- | Lift a stateful term homomorphism over signatures @f@ and @g@ to
-- a stateful term homomorphism over the same signatures, but extended with
-- annotations.
propAnnQ :: (DistAnn f p f', DistAnn g p g', HFunctor g)
        => QHom f q g -> QHom f' q g'
propAnnQ hm abv bel f' = ann p (hm abv bel f)
    where ((O.:&:) f p) = projectA f'

-- | Lift a bottom-up tree transducer over signatures @f@ and @g@ to a
-- bottom-up tree transducer over the same signatures, but extended
-- with annotations.
propAnnUp :: (DistAnn f p f', DistAnn g p g', HFunctor g)
        => UpTrans f q g -> UpTrans f' q g'
propAnnUp trans f' = (q :*: ann p t)
    where ((O.:&:) f p) = projectA f'
          (q :*: t) = trans f

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
pathAnn = runDownTrans trans [] where
    trans :: DownTrans g [Int] (g :&: [Int])
    trans q t = simpCxt (hfmap (\ (Numbered n s) -> appHFun s (K $ n:q)) (number t) :&: q)
