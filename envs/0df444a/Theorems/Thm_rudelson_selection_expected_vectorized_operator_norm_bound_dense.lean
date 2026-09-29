-- Prove2me | Theorems.Thm_rudelson_selection_expected_vectorized_operator_norm_bound_dense
-- name    : rudelson_selection_expected_vectorized_operator_norm_bound_dense
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T03:42:31.177772+00:00
-- url     : https://prove2.me/theorems/370e41e8-43c1-4dda-8798-3407cacc8c0f
-- statement:
--   Rudelson selection (CR2009 §9.1 / Rudelson 1999 JFA Thm 1, Steps 1-2 + self-bound feed): the expected operator norm of the vectorized centered Bernoulli rank-one tangent sum p⁻¹·‖∑(δ_ab−p)·(vec y_ab)(vec y_ab)*‖_op, with y_ab = P_T(coordinateMatrix a b), is bounded by Csym·(√(log(max n₁ n₂)/p)·R)·√(EZ+1) where EZ is the expected tangent sampling deviation. This packages the symmetrization (δ−p→εδ) plus matrix non-commutative Khintchine moment bound on the rank-one tensors plus the eq(2.1) self-bound feed, and composes with G1 (pointwise op-norm bound) to give Child-1.
-- source:
--   Candès–Recht 2009 (arXiv:0805.4471) §9.1 Thm 4.2; Rudelson 1999 JFA 164 Thm 1 Steps 1-2; Pisier §3 / Lust-Picquard NC-Khintchine.

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

theorem rudelson_selection_expected_vectorized_operator_norm_bound_dense :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) * Real.log (↑(max n₁ n₂)) →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1 : ℝ) else 0)
                      - (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2)
                          e.1 e.2)))))‖) ≤
          Csym *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          * Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) + 1) := by sorry
