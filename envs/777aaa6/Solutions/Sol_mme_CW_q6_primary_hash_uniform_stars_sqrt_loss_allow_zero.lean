-- Prove2me | solution 1 for mme_CW_q6_primary_hash_uniform_stars_sqrt_loss_allow_zero
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:10:00.309879+00:00
-- url     : https://prove2.me/submissions/6992bd7a-cf90-4bfc-a98c-d8f564677ea4

import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_CW_q6_zero_outer_exact_hash_family

open MME Filter


/-- The uniform star bound extends to zero outer mass by using all balanced
middle words in one exact star. -/
theorem solution
    (L G : ℕ → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let Zcount : ℕ := Nat.choose (2 * N) (L N) * Nat.choose (2 * N - L N) (L N)
        let Xcount : ℕ := Nat.choose N (G N)
        let middle : ℕ := Nat.choose (2 * G N) (G N)
        (L N + G N = N ∧ 341 * L N < 100 * G N) →
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N (L N) (G N) A H,
          H ≤ 4 ^ N ∧
          (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (middle : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss L G
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlarge] with N hN
  dsimp only at hN ⊢
  intro hprofile
  by_cases hzero : L N = 0
  · have hG : G N = N := by omega
    obtain ⟨family⟩ := mme_CW_q6_zero_outer_exact_hash_family N
    have hfamily : CWQ6PrimaryHashFamily N (L N) (G N) 1 (Nat.choose (2 * N) N) := by
      simpa only [hzero, hG] using family
    have hexp : Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (Real.sqrt_nonneg _)
    refine ⟨1, Nat.choose (2 * N) N, hfamily, ?_, ?_, ?_⟩
    · calc
        Nat.choose (2 * N) N ≤ 2 ^ (2 * N) := Nat.choose_le_two_pow _ _
        _ = 4 ^ N := by rw [pow_mul]; norm_num
    · simpa [hzero] using hexp
    · simp only [hG, Nat.choose_self, Nat.cast_one, one_pow, mul_one]
      have hnonneg : (0 : ℝ) ≤ (Nat.choose (2 * N) N : ℕ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hexp hnonneg]
  · exact hN ⟨Nat.pos_of_ne_zero hzero, hprofile.1, hprofile.2⟩


#print axioms solution
