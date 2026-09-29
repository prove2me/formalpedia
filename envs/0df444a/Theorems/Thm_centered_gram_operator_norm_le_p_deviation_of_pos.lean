-- Prove2me | Theorems.Thm_centered_gram_operator_norm_le_p_deviation_of_pos
-- name    : centered_gram_operator_norm_le_p_deviation_of_pos
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:36:22.810966+00:00
-- url     : https://prove2.me/theorems/8b16e13c-5cdc-419c-8651-7b12edb6b7e5
-- statement:
--   Fact (2) of the eq(2.1) self-bound (Candes-Recht 2009, Section 9.1), for $p>0$: the centered vectorized tangent Gram operator $G_c=\sum_{ab}(\delta_{ab}-p)\,\mathrm{vec}(P_T e_{ab})\otimes\mathrm{vec}(P_T e_{ab})$ has L2-operator norm at most $p\cdot Z$, where $Z=\mathrm{tangentSamplingDeviation}(\Omega,S,p)$. (The statement requires $p>0$; it fails at $p=0$ where $G_c$ is the nonzero sampled Gram but $Z=0$.)
-- source:
--   Candes, Recht, Exact Matrix Completion via Convex Optimization (2009), Section 9.1

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem centered_gram_operator_norm_le_p_deviation_of_pos
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 < p) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (((if ab ∈ Omega then (1 : Real) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖
      ≤ p * tangentSamplingDeviation Omega S p := by sorry
