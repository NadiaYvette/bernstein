%if False
\begin{code}
module Numeric.Polynomial.Bernstein where
-- import           "finite-typelits" Data.Finite (Finite)
import qualified "finite-typelits" Data.Finite as Finite ()

import           "vector-sized" Data.Vector.Sized (Vector) -- (Vector, MVector)
import qualified "vector-sized" Data.Vector.Sized as Vec (any, init, tail, zipWith)
import qualified "vector-sized" Data.Vector.Mutable.Sized as MVec ()

import            Data.Kind (Type)
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

Ugh.

\begin{code}
bernstein :: IO ()
bernstein = pure ()
\end{code}
