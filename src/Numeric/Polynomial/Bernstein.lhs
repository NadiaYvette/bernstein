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
import           "combinatorial"     Combinatorics (binomial)

import           "finite-typelits"   Data.Finite (Finite, finite, finites, getFinite)
import qualified "finite-typelits"   Data.Finite as Finite (strengthenN, weakenN)

import           "type-natural"      Data.Type.Natural

import           "vector-sized"      Data.Vector.Sized (Vector)
import qualified "vector-sized"      Data.Vector.Sized as Vec (any, fromList, index, init, map, tail, zipWith)
import qualified "vector-sized"      Data.Vector.Mutable.Sized as MVec ()

import           "base"              Data.Function (on)
import           "base"              Data.Kind (Type)
import           "base"              Data.Maybe (fromJust, fromMaybe)
import           "base"              Data.Proxy (Proxy (..))
import           "base"              Data.Ratio ((%))
import           "base"              GHC.TypeLits (KnownNat (..), Natural)
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

\begin{code}
b :: forall (n :: Nat) (reals :: Type) . ()
  => KnownNat n
  => Num reals
  => Finite n -> Bernstein n reals
b (fromIntegral . getFinite -> k) = Bernstein {..} where
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

From \cite[Ch.\ 4{\S}2,\ p.\ 13, eq.\ 43]{farouki:87}
\begin{equation}
\left(\sum_{k=0}^m a_k\cdot B_{m,k}\right)
  \cdot\left(\sum_{k=0}^n b_k\cdot B_{n,k}\right)
  = \frac{1}{\binom{m+n}{k}}
      \cdot\sum_{j=\max(0,k-n)}^{\min(m,k)}
              \binom{m}{j}\cdot\binom{n}{k-j}\cdot a_j\cdot b_{k-j}
\end{equation}

Degree reduction could make sense by producing both a difference and a
projection. Meanwhile, degree increase is much more straightforward.

From \cite[Ch.\ 3{\S}2,\ p.\ 10, eq.\ 27]{farouki:87}
\begin{equation}
\sum_{k=0}^n c_k\cdot B_{n,k}
  = \sum_{k=0}^{n+r} \frac{1}{\binom{n+r}{k}}
      \cdot\left(
        \sum_{j=\max(0,k-r)}^{\min(n,k)}
          \binom{r}{k-j}\cdot\binom{n}{j}\cdot c_j\right)
      \cdot B_{n+r,k}
\end{equation}
%if False
\begin{code}
(!) :: forall n reals . Vector n reals -> Finite n -> reals
(!) = Vec.index

infixl 6 <:-:>
infixl 7 <:*:>
(<:-:>), (<:*:>) :: forall t . KnownNat t => Finite t -> Finite t -> Finite t
m <:-:> k
  | m > k
  = m - k
  | otherwise
  = 0

m <:*:> k
  | m < k
  = k <:*:> m
  | m <= maxBound `div` k
  = m * k
  | otherwise
  = maxBound

finiteNat :: forall n . KnownNat n => Natural -> Finite n
finiteNat = finite . fromIntegral

chooseNat :: forall n . Finite n -> Finite n -> Natural
chooseNat = (fromIntegral .) . chooseInt

chooseInt :: forall n . Finite n -> Finite n -> Integer
chooseInt = binomial `on` getFinite

narrow :: forall (n :: Nat) (k :: Nat) . ()
  => KnownNat k
  -- |strengthenN| apparently makes no demands on its result type.
  -- Hence the below would be redundant:
  -- => k <= n
  -- More mysterious is why |KnownNat n| is also redundant.
  -- => KnownNat n
  => Finite n -> Finite k
narrow = fromMaybe maxBound . Finite.strengthenN

widen :: n <= m => Finite n -> Finite m
widen = Finite.weakenN
\end{code}
%endif
\begin{code}
raise :: forall (n :: Nat) (r :: Nat) (reals :: Type) . ()
  => KnownNat n
  => KnownNat r
  -- => n <= (n + r) -- I can see why this is redundant.
  -- => 1 <= r -- I'm less sure why this is redundant.
  => Fractional reals
  => Bernstein n reals -> Bernstein (n + r) reals
raise (Bernstein (c :: Vector (n + 1) reals)) = Bernstein {..} where
  nFinite :: Finite (n + 1) = maxBound
  rFinite :: Finite (r + 1) = maxBound
  nrFinite :: Finite (n + r + 1) = maxBound
  v :: Vector (n + r + 1) (Finite (n + r + 1))
  v = fromJust $ Vec.fromList (finites :: [Finite (n + r + 1)])
  bernsteinCoefficients :: Vector (n + r + 1) reals
  bernsteinCoefficients = flip Vec.map v \(k :: Finite (n + r + 1)) ->
    let jMin, jMax :: Finite (n + 1)
        jMin = fromMaybe maxBound . Finite.strengthenN
                 $ k <:-:> (Finite.weakenN rFinite :: Finite (n + r + 1))
        jMax = fromMaybe maxBound $ Finite.strengthenN k
    in sum $ flip map [jMin .. jMax] \(j :: Finite (n + 1)) ->
      let nrChooseK :: Integer
            = nrFinite
                `chooseInt` (widen (k - (widen j :: Finite (n + r + 1)))
                                     :: Finite (n + r + 1))
          nChooseJ :: Integer
            = (widen nFinite :: Finite (n + r + 1))
                `chooseInt` (widen j :: Finite (n + r + 1))
          rChooseKminusJ :: Integer
            = (widen rFinite :: Finite (n + r + 1))
                `chooseInt` (k <:-:> (widen j :: Finite (n + r + 1)))
      in fromRational (nChooseJ * rChooseKminusJ % nrChooseK) * (c ! j)
\end{code}

\begin{code}
bernstein :: IO ()
bernstein = pure ()
\end{code}
\printbibliography
\end{document}
