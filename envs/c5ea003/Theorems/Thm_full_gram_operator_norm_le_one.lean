-- Prove2me | Theorems.Thm_full_gram_operator_norm_le_one
-- name    : full_gram_operator_norm_le_one
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:36:03.952902+00:00
-- url     : https://prove2.me/theorems/386feadb-0a7c-42a8-a674-454c4abecac3
-- statement:
--   Fact (1) of the eq(2.1) self-bound (Candes-Recht 2009, Section 9.1): the full vectorized tangent Gram operator $G_f=\sum_{ab} \mathrm{vec}(P_T e_{ab})\otimes\mathrm{vec}(P_T e_{ab})$ equals the vectorized orthogonal tangent projector $P_T$, hence its L2-operator norm is at most $1$.
-- source:
--   Candes, Recht, Exact Matrix Completion via Convex Optimization (2009), Section 9.1

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem full_gram_operator_norm_le_one
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n1 × Fin n2,
          (1 : Real) •
            Matrix.vecMulVec
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n1 × Fin n2 =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖
      ≤ 1 := by sorry
