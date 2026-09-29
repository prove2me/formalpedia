-- Prove2me | Theorems.Thm_rudelson_selection_sampled_gram_self_bound_dense_of_pos
-- name    : rudelson_selection_sampled_gram_self_bound_dense_of_pos
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:43:57.201878+00:00
-- url     : https://prove2.me/theorems/c192493c-90e7-4cf9-90e9-70d878a52701
-- statement:
--   Rudelson selection self-bound (Candes-Recht 2009, Section 9.1 eq(2.1)), corrected to $p>0$: the L2-operator norm of the sampled uncentered vectorized rank-one tangent Gram $\sum_{ab\in\Omega} y_{ab}\otimes y_{ab}$, with $y_{ab}=\mathrm{vec}(P_T e_{ab})$, is at most $p(Z_\Omega+1)$ where $Z_\Omega$ is the tangent sampling deviation. Proof splits the sampled Gram into its expectation $pG_f$ plus the centered deviation $G_c$, bounds $\|G_f\|\le1$ and $\|G_c\|\le pZ$. (The unconditional $0\le p$ form is false at $p=0$.)
-- source:
--   Candes, Recht, Exact Matrix Completion via Convex Optimization (2009), Section 9.1

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem rudelson_selection_sampled_gram_self_bound_dense_of_pos
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 < p) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (if ab ∈ Omega then (1 : Real) else 0) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖
      ≤ p * (tangentSamplingDeviation Omega S p + 1) := by sorry
