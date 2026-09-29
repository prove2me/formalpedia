-- Prove2me | solution 1 for neumann_remainder_tangent_scale_le_half_from_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T07:51:03.617903+00:00
-- url     : https://prove2.me/submissions/a5ed0bb9-d689-4735-a3fa-5b61b060b14a

import Definitions.Def_matrix_completion_neumann
import Mathlib.Tactic

open MatrixCompletion

theorem solution
    (Cdev : ℝ) :
    ∃ CR : ℝ, 0 < CR ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n r m : ℕ) (μ₀ : ℝ),
        0 < n → 0 < r → 1 ≤ μ₀ →
        (m : ℝ) ≥ CR * μ₀ * (n : ℝ) * (r : ℝ) *
          (β * Real.log (n : ℝ)) →
        tangentSamplingDeviationScale Cdev β μ₀ n r m ≤ (1 : ℝ) / 2 := by
  refine ⟨max 1 (4 * Cdev ^ 2), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro β hβ n r m μ₀ hn hr hμ₀ hmLower
    let CR : ℝ := max 1 (4 * Cdev ^ 2)
    let A : ℝ := μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))
    have hCR_pos : 0 < CR := by
      dsimp [CR]
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hCR_nonneg : 0 ≤ CR := le_of_lt hCR_pos
    have hn_real_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hn)
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_real_ge_one
    have hbeta_nonneg : 0 ≤ β := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 2) hβ)
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    by_cases hA_zero : A = 0
    · unfold tangentSamplingDeviationScale
      have hnum :
          μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ)) = 0 := hA_zero
      simp [hnum]
    · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA_zero)
      have hm_pos : 0 < (m : ℝ) := by
        have hpos : 0 < CR * A := mul_pos hCR_pos hA_pos
        have hmLower' : (m : ℝ) ≥ CR * A := by
          simpa [CR, A, mul_assoc] using hmLower
        exact lt_of_lt_of_le hpos hmLower'
      have hratio_le :
          A / (m : ℝ) ≤ 1 / CR := by
        rw [div_le_div_iff₀ hm_pos hCR_pos]
        have hmLower' : (m : ℝ) ≥ CR * A := by
          simpa [CR, A, mul_assoc] using hmLower
        nlinarith
      have hratio_nonneg : 0 ≤ A / (m : ℝ) := div_nonneg hA_nonneg (le_of_lt hm_pos)
      have hsqrt_le : Real.sqrt (A / (m : ℝ)) ≤ Real.sqrt (1 / CR) :=
        Real.sqrt_le_sqrt hratio_le
      have hsqrtCR_sq :
          (Real.sqrt (1 / CR)) ^ 2 = 1 / CR := by
        exact Real.sq_sqrt (div_nonneg zero_le_one hCR_nonneg)
      have hCR_ge : 4 * Cdev ^ 2 ≤ CR := by
        dsimp [CR]
        exact le_max_right _ _
      by_cases hCdev_nonpos : Cdev ≤ 0
      · unfold tangentSamplingDeviationScale
        have hsqrt_nonneg : 0 ≤ Real.sqrt
            ((μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) / (m : ℝ)) :=
          Real.sqrt_nonneg _
        nlinarith
      · have hCdev_pos : 0 < Cdev := lt_of_not_ge hCdev_nonpos
        have hsqrt_bound : Cdev * Real.sqrt (1 / CR) ≤ (1 : ℝ) / 2 := by
          have hsq :
              (Cdev * Real.sqrt (1 / CR)) ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by
            rw [mul_pow, hsqrtCR_sq]
            have hdiv : Cdev ^ 2 / CR ≤ (1 : ℝ) / 4 := by
              rw [div_le_iff₀ hCR_pos]
              nlinarith
            have hdiv' : Cdev ^ 2 * (1 / CR) ≤ (1 : ℝ) / 4 := by
              simpa [div_eq_mul_inv, one_div] using hdiv
            nlinarith
          have hleft_nonneg : 0 ≤ Cdev * Real.sqrt (1 / CR) :=
            mul_nonneg (le_of_lt hCdev_pos) (Real.sqrt_nonneg _)
          exact (sq_le_sq₀ hleft_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)).mp hsq
        unfold tangentSamplingDeviationScale
        have hsqrt_actual_le :
            Real.sqrt
                ((μ₀ * (n : ℝ) * (r : ℝ) * (β * Real.log (n : ℝ))) /
                  (m : ℝ)) ≤
              Real.sqrt (1 / CR) := by
          simpa [A, mul_assoc] using hsqrt_le
        exact le_trans
          (mul_le_mul_of_nonneg_left hsqrt_actual_le (le_of_lt hCdev_pos))
          hsqrt_bound
