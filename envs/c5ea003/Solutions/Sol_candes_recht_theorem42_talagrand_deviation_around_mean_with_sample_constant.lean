-- Prove2me | solution 1 for candes_recht_theorem42_talagrand_deviation_around_mean_with_sample_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-29T15:41:32.432867+00:00
-- url     : https://prove2.me/submissions/e4b913e3-9620-4a4d-922e-1751a08e883e

import Theorems.Thm_candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail
import Theorems.Thm_bernoulli_event_prob_nonneg
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

/-!
Source: Candes--Recht, PDF p. 19, Theorem 4.2 equation (4.10), and Appendix
9.1, PDF pp. 46--47, Theorem 9.1/equation (9.2).

This replaces the deprecated square-root-only Talagrand route.  For `m > 0`,
it invokes the source-faithful Appendix 9.1 logarithmic-tail decomposition.
For the formal corner case `m = 0`, the paper's division by `m` is not used:
the sample lower bound either contradicts `max n₁ n₂ > 1`, or forces
`max n₁ n₂ = 1`, where an enlarged universal failure constant makes the
required lower bound nonpositive.
-/
theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → A0 S μ₀ →
        (m : ℝ) ≥
          C' * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂))) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 1 →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (bernoulliExpectation
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                    (fun Omega' =>
                      tangentSamplingDeviation Omega' S
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) +
                  tangentSamplingDeviationScale C β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases candes_recht_theorem42_talagrand_positive_samples_from_appendix91_log_tail with
    ⟨Cpos, cpos, hCpos, hcpos, hPositive⟩
  refine ⟨Cpos, max cpos 1, hCpos, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ S hn₁ hn₂ hr hm hμ₀ hA0 hmLower hEZ
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let Event : Finset (Fin n₁ × Fin n₂) → Prop :=
    fun Omega =>
      TangentSamplingDeviationBound Omega S p
        (bernoulliExpectation p
          (fun Omega' => tangentSamplingDeviation Omega' S p) +
          tangentSamplingDeviationScale Cpos β μ₀ (max n₁ n₂) r m)
  have hcpos_le : cpos ≤ max cpos 1 := le_max_left _ _
  have hpow_nonneg : 0 ≤ Real.rpow (↑(max n₁ n₂) : ℝ) (-β) :=
    Real.rpow_nonneg (by positivity) _
  by_cases hmpos : 0 < m
  · have hpos :
        bernoulliEventProb p Event ≥
          1 - cpos * Real.rpow (↑(max n₁ n₂)) (-β) := by
      simpa [p, Event] using
        hPositive C' hC' β hβ n₁ n₂ r m M μ₀ S
          hn₁ hn₂ hr hmpos hm hμ₀ hA0 hmLower hEZ
    have hmono :
        1 - cpos * Real.rpow (↑(max n₁ n₂)) (-β) ≥
          1 - max cpos 1 * Real.rpow (↑(max n₁ n₂)) (-β) := by
      nlinarith [mul_le_mul_of_nonneg_right hcpos_le hpow_nonneg]
    exact le_trans hmono hpos
  · have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmpos
    have hp_bounds := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
    have hprob_nonneg : 0 ≤ bernoulliEventProb p Event :=
      bernoulli_event_prob_nonneg Event hp_bounds.1 hp_bounds.2
    by_cases hmax_one : max n₁ n₂ = 1
    · have htarget_nonpos :
          1 - max cpos 1 * Real.rpow (↑(max n₁ n₂) : ℝ) (-β) ≤ 0 := by
        have hone : Real.rpow (↑(max n₁ n₂) : ℝ) (-β) = 1 := by
          simp [hmax_one]
        have hcle : (1 : ℝ) ≤ max cpos 1 := le_max_right _ _
        rw [hone]
        nlinarith
      exact le_trans htarget_nonpos hprob_nonneg
    · have hmax_pos_nat : 0 < max n₁ n₂ := lt_max_of_lt_left hn₁
      have hmax_gt_one : 1 < max n₁ n₂ := by
        omega
      have hlog_pos : 0 < Real.log (↑(max n₁ n₂) : ℝ) := by
        exact Real.log_pos (by exact_mod_cast hmax_gt_one)
      have hC'pos : 0 < C' := lt_of_lt_of_le hCpos hC'
      have hμpos : 0 < μ₀ := lt_of_lt_of_le zero_lt_one hμ₀
      have hrpos_real : 0 < (r : ℝ) := by exact_mod_cast hr
      have hmaxpos_real : 0 < (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax_pos_nat
      have hβpos : 0 < β := lt_trans (by norm_num) hβ
      have hprod_pos :
          0 <
            C' * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
        positivity
      have hzero_ge :
          (0 : ℝ) ≥
            C' * μ₀ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂) : ℝ)) := by
        simpa [hmzero] using hmLower
      exact False.elim (not_lt_of_ge hzero_ge hprod_pos)
