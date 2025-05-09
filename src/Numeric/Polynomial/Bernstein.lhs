\documentclass{article}
%include polycode.fmt
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage[backend=bibtex]{biblatex}
\usepackage{comment}
\usepackage{url}
\addbibresource{farouki.bib}
\begin{document}
%if False
\begin{code}
module Numeric.Polynomial.Bernstein where
import           "finite-typelits" Data.Finite (Finite)
import qualified "finite-typelits" Data.Finite as Finite (getFinite)

import           "vector-sized" Data.Vector.Sized (Vector) -- (Vector, MVector)
import qualified "vector-sized" Data.Vector.Sized as Vec (any, fromList, init, map, tail, zipWith)
import qualified "vector-sized" Data.Vector.Mutable.Sized as MVec ()

import            Data.Kind (Type)
import            Data.Maybe (fromJust)
import            Data.Proxy (Proxy (..))
-- import            Data.Type.Equality ((:~:)(..), TestEquality (..))
import           "type-natural" Data.Type.Natural

import            GHC.TypeLits (KnownNat (..), Natural)
\end{code}
%endif
\begin{code}
newtype Bernstein (n :: Nat) reals
  = Bernstein { bernsteinCoefficients :: Vector (n + 1) reals }
\end{code}

This actually returns $\deg p + 1$ when the vector represents
polynomial coefficients.

\begin{spec}
deg' :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat n
  => Eq reals
  => Num reals
  => Bernstein n reals -> Natural
deg' (Bernstein v) = case natSing :: SNat n of
  Succ _ | Vec.any (/= 0) v
         -> succ . deg' $ Vec.zipWith subtract (Vec.tail v) (Vec.init v)
         | otherwise -> 0
  Zero | Vec.any (/= 0) v -> 1
       | otherwise -> 0
\end{spec}

\begin{code}
degRec :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat (n+1)
  => Eq reals
  => Num reals
  => (forall (k :: Nat) . KnownNat k => Vector k reals -> Natural) -> Vector (n+1) reals -> Natural
degRec f v
  | Vec.any (/= 0) v
  , initV :: Vector n reals <- Vec.init v
  , tailV :: Vector n reals <- Vec.tail v
  , v' :: Vector n reals <- Vec.zipWith subtract tailV initV
  = 1 + f v'
  | otherwise
  = 0
\end{code}

\begin{code}
fixDegRec :: forall (k :: Nat) (reals :: Type) . ()
  => KnownNat k
  => Eq reals
  => Num reals
  => Vector k reals -> Natural
fixDegRec v = case natSing :: SNat k of
  Succ _ | Vec.any (/= 0) v -> degRec fixDegRec v
         | otherwise -> 0
  Zero | Vec.any (/= 0) v -> 1
       | otherwise -> 0
\end{code}

\begin{code}
deg :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat n
  => Eq reals
  => Num reals
  => Bernstein n reals -> Natural
deg (Bernstein v) = degRec fixDegRec v
\end{code}

\begin{equation}
\frac{d}{dt}\sum_{k=0}^{n+1} c_k\cdot B_{n+1,k}
  = (n+1)\sum_{k=0}^n (c_{k+1}-c_k)\cdot B_{n,k}
\end{equation}

\begin{code}
diff :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat n
  => Num reals
  => Bernstein (n+1) reals -> Bernstein n reals
diff (Bernstein v) = Bernstein {..} where
  bernsteinCoefficients = Vec.zipWith combine (Vec.init v) (Vec.tail v)
  n' = natVal (Proxy :: Proxy (n + 1))
  combine = (((fromIntegral n') *) .) . subtract
\end{code}

Degree reduction could make sense by producing both a difference and a
projection. Meanwhile, degree increase is much more straightforward.

\begin{equation}
\sum_{k=0}^n c_k\cdot B_{n,k}
  = \sum_{k=0}^{n+r} \frac{1}{\binom{n+r}{k}}
      \cdot\left(
        \sum_{j=\max(0,k-r)}^{\min(n,k)}
          \binom{r}{k-j}\cdot\binom{n}{j}\cdot c_j\right)
      \cdot B_{n+r,k}
\end{equation}

\begin{code}
b :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat n
  => Num reals
  => Finite n -> Bernstein n reals
b (fromIntegral . Finite.getFinite -> k) = Bernstein {..} where
  n = natVal (Proxy :: Proxy n)
  bernsteinCoefficients = fromJust
    $ Vec.fromList [if j == k then 1 else 0 | j <- [0..n]]
\end{code}

\begin{code}
instance (KnownNat n, Num reals) => Num (Bernstein n reals) where
  abs _ = error "Bernstein: abs unimplemented"
  signum _ = error "Bernstein: abs unimplemented"
  fromInteger k = Bernstein . fromJust . Vec.fromList
    $ replicate (fromIntegral $ natVal (Proxy :: Proxy (n+1))) (fromIntegral k)
  negate (Bernstein f) = Bernstein $ Vec.map negate f
  Bernstein f + Bernstein g = Bernstein
    $ Vec.zipWith (+) f g
  _ * _ = error "Bernstein: (*) unimplemented"
\end{code}

\begin{equation}
\left(\sum_{k=0}^m a_k\cdot B_{m,k}\right)
  \cdot\left(\sum_{k=0}^n b_k\cdot B_{n,k}\right)
  = \frac{1}{\binom{m+n}{k}}
      \cdot\sum_{j=\max(0,k-n)}^{\min(m,k)}
              \binom{m}{j}\cdot\binom{n}{k-j}\cdot a_j\cdot b_{k-j}
\end{equation}

\begin{spec}
raise :: forall (n :: Nat) (r :: Nat) (reals :: Type) . ()
  => KnownNat n
  => KnownNat r
  => Num reals
  => Bernstein n reals -> Bernstein (n + r) reals
raise = pure ()
\end{spec}

\begin{code}
bernstein :: IO ()
bernstein = pure ()
\end{code}
\end{document}
