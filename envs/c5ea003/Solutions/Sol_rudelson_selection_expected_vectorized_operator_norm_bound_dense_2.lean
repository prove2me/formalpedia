-- Prove2me | solution 2 for rudelson_selection_expected_vectorized_operator_norm_bound_dense
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T02:44:21.053025+00:00
-- url     : https://prove2.me/submissions/745f044f-938f-49fd-8b54-c330592f8217

import Theorems.Thm_rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
import Theorems.Thm_rudelson_selection_sampled_gram_self_bound_dense_of_pos
import Theorems.Thm_bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
import Theorems.Thm_sample_ratio_between_zero_and_one
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

theorem solution :
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
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) + 1) := by
  rcases rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense with
    ⟨Csym, hCsym_pos, hEngine⟩
  refine ⟨Csym, hCsym_pos, ?_⟩
  intro β hβ n₁ n₂ r m M S R hn₁ hn₂ hr hmle hR _hsample hcoord
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp_bounds := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hmle
  have hp0 : 0 ≤ p := by simpa [p] using hp_bounds.1
  have hp1 : p ≤ 1 := by simpa [p] using hp_bounds.2
  have hEngineInst :=
    hEngine n₁ n₂ r m M S R hn₁ hn₂ hr hmle hR hcoord
  by_cases hpzero : p = 0
  · have hp_expr : ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by
      simpa [p] using hpzero
    simpa [hp_expr, bernoulliExpectation] using (le_rfl : (0 : ℝ) ≤ 0)
  · have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpzero)
    have hBridge :
        bernoulliExpectation p
            (fun Omega =>
              Real.sqrt
                (p⁻¹ *
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                    (∑ ab : Fin n₁ × Fin n₂,
                      (if ab ∈ Omega then (1 : ℝ) else 0) •
                        Matrix.vecMulVec
                          (fun e : Fin n₁ × Fin n₂ =>
                            tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                          (fun e : Fin n₁ × Fin n₂ =>
                            tangentProjection S (coordinateMatrix ab.1 ab.2)
                              e.1 e.2))))‖)) ≤
          Real.sqrt
            (bernoulliExpectation p
              (fun Omega => tangentSamplingDeviation Omega S p) + 1) := by
      refine
        bernoulli_expectation_sqrt_self_bound_of_positive_rate_pointwise_gram_bound
          (n₁ := n₁) (n₂ := n₂) (p := p) hp_pos hp1
          (fun Omega =>
            ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
              (∑ ab : Fin n₁ × Fin n₂,
                (if ab ∈ Omega then (1 : ℝ) else 0) •
                  Matrix.vecMulVec
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2)
                        e.1 e.2))))‖)
          (fun Omega => tangentSamplingDeviation Omega S p) ?_ ?_
      · intro Omega
        exact norm_nonneg _
      · intro Omega
        exact rudelson_selection_sampled_gram_self_bound_dense_of_pos S Omega p hp_pos
    have hpref_nonneg :
        0 ≤ Csym * (Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R) := by
      exact mul_nonneg hCsym_pos.le (mul_nonneg (Real.sqrt_nonneg _) hR)
    have hmul :=
      mul_le_mul_of_nonneg_left hBridge hpref_nonneg
    exact le_trans (by simpa [p] using hEngineInst) (by simpa [p, mul_assoc] using hmul)
