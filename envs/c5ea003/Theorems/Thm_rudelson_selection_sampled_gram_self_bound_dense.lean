-- Prove2me | Theorems.Thm_rudelson_selection_sampled_gram_self_bound_dense
-- name    : rudelson_selection_sampled_gram_self_bound_dense
-- status  : Disproved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T04:21:18.2836+00:00
-- url     : https://prove2.me/theorems/59399091-0ed4-4190-9d35-a16d3e1984d5
-- statement:
--   Rudelson 1999 (JFA 164) Thm 1 / CR2009 (arXiv:0805.4471) section 9.1 eq(2.1) self-bound feed: the operator norm of the sampled (uncentered) vectorized rank-one Gram sum of the tangent coordinate images y_ab = P_T(e_a e_b*), namely sum over ab in Omega of (y_ab tensor y_ab), is bounded by p*(Z_Omega + 1) where Z_Omega = tangentSamplingDeviation Omega S p is the variational operator-norm tangent sampling deviation. This is the self-protection step ||P_T P_Omega P_T|| <= p(Z+1) from ||P_T P_Omega P_T - p P_T|| <= p Z and ||P_T||=1.
-- source:
--   Rudelson 1999 JFA 164 Thm 1 (eq 2.1); Candes-Recht 2009 arXiv:0805.4471 section 9.1.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

/-
S7 CARVE (the ONE Mathlib-absent atom of the Rudelson §9.1 route).

Rudelson 1999 (JFA 164) Thm 1 / CR2009 §9.1 eq(2.1) self-bound FEED:
the operator norm of the *sampled* (uncentered) vectorized rank-one Gram sum
`∑_{ab∈Ω} y_ab ⊗ y_ab` is controlled by `p·(Z_Ω + 1)`, where
`y_ab = P_T(e_a e_b*) = tangentProjection S (coordinateMatrix a b)` and
`Z_Ω = tangentSamplingDeviation Ω S p`.

This is the genuinely Mathlib-absent operator-space content of the route (it
encodes `‖P_T P_Ω P_T‖ ≤ p(Z+1)` via the variational deviation `Z`), and is
carved as a single Open sub-node.
-/
theorem rudelson_selection_sampled_gram_self_bound_dense
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (if ab ∈ Omega then (1 : Real) else 0) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖
      ≤ p * (tangentSamplingDeviation Omega S p + 1) := by
  sorry
