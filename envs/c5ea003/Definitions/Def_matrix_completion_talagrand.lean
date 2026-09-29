-- Prove2me | Definitions.Def_matrix_completion_talagrand
-- name    : matrix_completion_talagrand
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:57:27.923594+00:00
-- url     : https://prove2.me/theorems/c6ac46db-36c4-496f-9f82-cb0a08258e2f
-- statement:
--   This definition module provides Talagrand/Rudelson concentration interfaces for tangent-space sampling deviation.
--
--   $$
--   \sup_{X\in T,\ \|X\|_F=1}
--   \left|\langle(P_\Omega-pI)X,X\rangle\right|.
--   $$
--
--   Module overview: Talagrand concentration interfaces for the tangent sampling deviation. Appendix 9.1 rewrites the tangent sampling deviation as a supremum over bilinear forms indexed by two Frobenius-unit tangent matrices. The definitions below expose the coefficient, bounded-increment condition, and variance condition used to apply Talagrand's product-space concentration theorem.
--
--   Documented declarations:
--   1. Coefficient of the centered Bernoulli variable at coordinate $(i,j)$ in the Talagrand supremum representation of the tangent sampling deviation.
--   2. Uniform boundedness hypothesis $|f| \le B$ for Talagrand's theorem in the tangent sampling deviation application.
--   3. Variance hypothesis σ² for Talagrand's theorem in the tangent sampling deviation application.
--
--   Role in the mission. Key declarations include tangentSamplingTalagrandCoefficient, TangentSamplingTalagrandIncrementBound, TangentSamplingTalagrandVarianceBound. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

/-!
Talagrand concentration interfaces for the tangent sampling deviation.

Appendix 9.1 rewrites the tangent sampling deviation as a supremum over
bilinear forms indexed by two Frobenius-unit tangent matrices.  The definitions
below expose the coefficient, bounded-increment condition, and variance
condition used to apply Talagrand's product-space concentration theorem.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Coefficient of the centered Bernoulli variable at coordinate `(i,j)` in the
Talagrand supremum representation of the tangent sampling deviation. -/
noncomputable def tangentSamplingTalagrandCoefficient
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (p : Real) (X1 X2 : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    Real :=
  p⁻¹ *
    matrixInner X1 (tangentProjection S (coordinateMatrix i j)) *
      matrixInner (tangentProjection S (coordinateMatrix i j)) X2

/-- Uniform boundedness hypothesis `|f| ≤ B` for Talagrand's theorem in the
tangent sampling deviation application. -/
def TangentSamplingTalagrandIncrementBound
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (p B : Real) : Prop :=
  ∀ X1 X2 : RealMatrix n1 n2,
    frobeniusNorm X1 ≤ 1 →
    frobeniusNorm X2 ≤ 1 →
    ∀ i : Fin n1, ∀ j : Fin n2,
      |tangentSamplingTalagrandCoefficient S p X1 X2 i j| ≤ B

/-- Variance hypothesis `σ²` for Talagrand's theorem in the tangent sampling
deviation application. -/
def TangentSamplingTalagrandVarianceBound
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (p sigmaSq : Real) : Prop :=
  ∀ X1 X2 : RealMatrix n1 n2,
    frobeniusNorm X1 ≤ 1 →
    frobeniusNorm X2 ≤ 1 →
      ∑ i : Fin n1, ∑ j : Fin n2,
        p * (1 - p) *
          (tangentSamplingTalagrandCoefficient S p X1 X2 i j) ^ 2 ≤
        sigmaSq

end MatrixCompletion


