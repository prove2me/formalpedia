-- Prove2me | solution 1 for rudelson_selection_symmetrized_tensor_khintchine_dense
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T03:42:42.28687+00:00
-- url     : https://prove2.me/submissions/19babd1c-0a28-4f1b-83d8-2918ae778d4f

import Theorems.Thm_tangent_sampling_deviation_le_vectorized_operator_norm
import Theorems.Thm_rudelson_selection_expected_vectorized_operator_norm_bound_dense
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

/-
CHILD 1 (2479e5b5) assembly = a 2-line reduction onto:
  G1   tangent_sampling_deviation_le_vectorized_operator_norm  (Proved)
  NB-4 rudelson_selection_expected_vectorized_operator_norm_bound_dense  (bot6's
       Rudelson Step-2 NC-Khintchine bypass lane; clean child stub for now)

  EZ = 𝔼_Ω[tsd Ω S p]
     ≤ 𝔼_Ω[p⁻¹·‖A_Ω‖_op]        (G1 pointwise + Bernoulli-weight monotonicity)
     ≤ Csym·(√(log max/p)·R)·√(EZ+1)   (NB-4)

with A_Ω = ∑_{ab}(δ_ab−p)·(vec y_ab)(vec y_ab)^*, y_ab = P_T(e_a e_b^*),
p = m/(n₁n₂).  Source: Rudelson 1999 JFA 164 Thm 1 Steps 1-2; CR2009 §9.1.
-/
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
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Csym *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          * Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) + 1) := by
  obtain ⟨Csym, hCsym_pos, hNB4⟩ :=
    rudelson_selection_expected_vectorized_operator_norm_bound_dense
  refine ⟨Csym, hCsym_pos, ?_⟩
  intro β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hR hdens hcoord
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- 0 < p ≤ 1 from the dimensions and m ≤ n₁n₂.
  have hn1R : (0:ℝ) < (n₁ : ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂ : ℝ) := by exact_mod_cast hn2
  have hmRle : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    rwa [Nat.cast_mul] at this
  have hp_nn : 0 ≤ p := by rw [hp_def]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]; exact hmRle
  have hpinv_nn : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_nn
  -- abbreviation for the per-Ω vectorized operator-norm summand.
  set A : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega =>
      p⁻¹ *
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n₁ × Fin n₂,
          (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
            Matrix.vecMulVec
              (fun e : Fin n₁ × Fin n₂ =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n₁ × Fin n₂ =>
                tangentProjection S (coordinateMatrix ab.1 ab.2)
                  e.1 e.2)))))‖ with hA_def
  -- STEP 1: EZ ≤ 𝔼_Ω[A Ω]  (G1 pointwise + weight monotonicity).
  have hstep1 :
      bernoulliExpectation p (fun Omega => tangentSamplingDeviation Omega S p)
        ≤ bernoulliExpectation p A := by
    unfold bernoulliExpectation
    apply Finset.sum_le_sum
    intro Omega _
    have hw : 0 ≤ bernoulliObservationWeight p Omega := by
      unfold bernoulliObservationWeight
      exact mul_nonneg (pow_nonneg hp_nn _) (pow_nonneg (by linarith) _)
    apply mul_le_mul_of_nonneg_left _ hw
    -- G1 pointwise bound.
    have hG1 := tangent_sampling_deviation_le_vectorized_operator_norm
      S Omega p hpinv_nn
    rw [hA_def]
    exact hG1
  -- STEP 2: 𝔼_Ω[A Ω] ≤ Csym·(√(log max/p)·R)·√(EZ+1)  (NB-4).
  have hstep2 := hNB4 β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hR hdens hcoord
  -- NB-4's LHS is `bernoulliExpectation p A` once p, A are folded.
  rw [← hp_def, ← hA_def] at hstep2
  -- chain.
  exact le_trans hstep1 hstep2
