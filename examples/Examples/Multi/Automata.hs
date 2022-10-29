{-# LANGUAGE RankNTypes, TypeOperators, TypeApplications, ScopedTypeVariables, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Automata
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines tree automata based on compositional data types.
--
--------------------------------------------------------------------------------

module Examples.Multi.Automata where

import Data.Maybe
import Control.Monad

import Data.Comp.Multi
import Data.Comp.Multi.HTraversable
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.Ops

{-| This type represents transition functions of deterministic
bottom-up tree acceptors (DUTAs).  -}

type DUTATrans f q = Alg f (K q)

{-| This data type represents deterministic bottom-up tree acceptors (DUTAs).
-}
data DUTA f q = DUTA {
      dutaTrans :: DUTATrans f q,
      dutaAccept :: q -> Bool
    }

{-| This function runs the transition function of a DUTA on the given
term. -}

runDUTATrans :: HFunctor f => DUTATrans f q -> Term f :-> K q
runDUTATrans = cata

{-| This function checks whether a given DUTA accepts a term.  -}

duta :: HFunctor f => DUTA f q -> Term f i -> Bool
duta DUTA{dutaTrans = trans, dutaAccept = accept} = accept . unK . runDUTATrans trans

{-| This type represents transition functions of non-deterministic
bottom-up tree acceptors (NUTAs).  -}

type NUTATrans f q = AlgM [] f (K q)


{-| This type represents non-deterministic bottom-up tree acceptors.
-}
data NUTA f q = NUTA {
      nutaTrans :: NUTATrans f q,
      nutaAccept :: q -> Bool
    }

{-| This function runs the given transition function of a NUTA on the
given term -}

runNUTATrans :: HTraversable f => NUTATrans f q -> Term f i -> [q]
runNUTATrans trans = map unK . cataM trans

{-| This function checks whether a given NUTA accepts a term. -}

nuta :: HTraversable f => NUTA f q -> Term f i -> Bool
nuta NUTA{nutaTrans = trans, nutaAccept = accept} = any accept . runNUTATrans trans


{-| This function determinises the given NUTA.  -}

-- algM :: (HTraversable f, Monad m) => AlgM m f a -> Alg f (m a)
-- algM f x = sequence x >>= f
--

sequenceK :: (HTraversable f, Monad m) => f (K (m q)) i -> m (f (K q) i)
sequenceK x = htraverse (fmap K . unK) x

algM :: (HTraversable f, Monad m) => (f (K q) i -> m (K q i)) -> f (K (m q)) i -> K (m q) i
algM f x = K . fmap unK $ sequenceK x >>= f

determNUTA :: (HTraversable f) => NUTA f q -> DUTA f [q]
determNUTA n = DUTA
               { dutaTrans = algM $ nutaTrans n
               , dutaAccept = any $ nutaAccept n
               }

{-| This function represents transition functions of
deterministic bottom-up tree transducers (DUTTs).  -}

type DUTTTrans f g q = forall a. f (K q :*: a) :-> (K q :*: Cxt Hole g a)

{-| This function transforms a DUTT transition function into an
algebra.  -}

instance HFunctor ((:*:) q) where
  hfmap f (a :*: b) = a :*: f b

-- type Alg f e = f e :-> e
-- f (K q :*: Term g) :-> (K q :*: Term g)
duttTransAlg :: (HFunctor f, HFunctor g)  => DUTTTrans f g q -> Alg f (K q :*: Term g)
duttTransAlg trans = hfmap injectCxt . trans

{-| This function runs the given DUTT transition function on the given
term.  -}

-- Expected type: (          f (K q :*: a0) i1  -> (K q :*: Cxt Hole g a0) i1   -> f (K q :*: Term g) i0 -> (K q :*: Term g) i0
-- Actual   type: (forall a. f (K q :*: a )    :-> (K q :*: Cxt Hole g a  )   ) -> f (K q :*: Term g)   :-> (K q :*: Term g)


runDUTTTrans :: forall f g q . (HFunctor f, HFunctor g)  => DUTTTrans f g q -> Term f :-> (K q :*: Term g)
runDUTTTrans trans = cata (duttTransAlg trans)

{-| This data type represents deterministic bottom-up tree
transducers. -}

data DUTT f g q = DUTT {
      duttTrans :: DUTTTrans f g q,
      duttAccept :: q -> Bool
    }

{-| This function transforms the given term according to the given
DUTT and returns the resulting term provided it is accepted by the
DUTT. -}

dutt :: (HFunctor f, HFunctor g) => DUTT f g q -> Term f i -> Maybe (Term g i)
dutt DUTT{duttTrans = trans, duttAccept = accept} = accept' . runDUTTTrans trans
    where accept' (K q :*: res)
              | accept q = Just res
              | otherwise = Nothing

{-| This type represents transition functions of non-deterministic
bottom-up tree transducers (NUTTs).  -}

type NUTTTrans f g q = forall a i . f (K q :*: a) i -> [(K q :*: Cxt Hole g a) i]

{-| This function transforms a NUTT transition function into a monadic
algebra.  -}

nuttTransAlg :: (HFunctor f, HFunctor g)  => NUTTTrans f g q -> AlgM [] f (K q :*: Term g)
nuttTransAlg trans = liftM (hfmap injectCxt) . trans

{-| This function runs the given NUTT transition function on the given
term.  -}

-- f0 (K q0 :*: Term g0) i0 -> [(:*:) (K q0) (Term g0) i0]

runNUTTTrans :: (HTraversable f, HFunctor g)  => NUTTTrans f g q -> forall i . (Term f i -> [(K q :*: Term g) i])
runNUTTTrans trans = cataM (nuttTransAlg trans)

{-| This data type represents non-deterministic bottom-up tree
transducers (NUTTs). -}

data NUTT f g q = NUTT {
      nuttTrans :: NUTTTrans f g q,
      nuttAccept :: q -> Bool
    }

{-| This function transforms the given term according to the given
NUTT and returns a list containing all accepted results. -}

nutt :: (HTraversable f, HFunctor g) => NUTT f g q -> Term f i -> [Term g i]
nutt NUTT{nuttTrans = trans, nuttAccept = accept} = mapMaybe accept' . runNUTTTrans trans
    where accept' (K q :*: res)
              | accept q = Just res
              | otherwise = Nothing
