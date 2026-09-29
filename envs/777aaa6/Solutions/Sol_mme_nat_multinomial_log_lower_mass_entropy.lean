-- Prove2me | solution 1 for mme_nat_multinomial_log_lower_mass_entropy
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T01:19:21.759987+00:00
-- url     : https://prove2.me/submissions/10465b2c-8030-49c2-8f00-6f707b9c89fd

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Definitions.Def_mme_regional_entropy_rate_data
open scoped BigOperators
set_option autoImplicit false

theorem solution {R : Type*} [Fintype R] (w : R → ℕ) :
    MME.RegionRate.massEntropy (fun i => (w i : ℝ)) -
        (Fintype.card R : ℝ) * Real.log (6 * (((∑ i, w i : ℕ) : ℝ) + 1)) ≤
      Real.log (((∑ i, w i).factorial / ∏ i, (w i).factorial : ℕ) : ℝ) := by
  classical
  have hsum : (∑ i, (w i : ℝ)) = ((∑ i, w i : ℕ) : ℝ) := by push_cast; rfl
  set W : ℕ := ∑ i, w i with hWdef
  have hcardlog : 0 ≤ (Fintype.card R : ℝ) * Real.log (6 * ((W : ℝ) + 1)) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    have : (0:ℝ) ≤ W := by positivity
    linarith
  rcases Nat.eq_zero_or_pos W with h0 | hpos
  · -- all entries vanish
    have hw0 : ∀ i, w i = 0 := by
      intro i
      have := Finset.single_le_sum (f := w) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hm : MME.RegionRate.massEntropy (fun i => (w i : ℝ)) = 0 := by
      unfold MME.RegionRate.massEntropy MME.RegionRate.entropy
      simp [hw0]
    have hr : ((W.factorial / ∏ i, (w i).factorial : ℕ) : ℝ) = 1 := by
      rw [h0]; simp [hw0]
    rw [hm, hr, Real.log_one]
    linarith
  · have hW : (0:ℝ) < W := by exact_mod_cast hpos
    have hl2 : Real.log 2 ≠ 0 := by positivity
    have hmass : MME.RegionRate.massEntropy (fun i => (w i : ℝ)) =
        (W : ℝ) * Real.log 2 * mme_modern_entropyBits (fun i ↦ (w i : ℝ) / (W : ℝ)) := by
      unfold MME.RegionRate.massEntropy MME.RegionRate.entropy mme_modern_entropyBits
      rw [mul_assoc, mul_div_cancel₀ _ hl2, Finset.mul_sum]
      rw [hsum]
      have hterm : ∀ i, (W : ℝ) * Real.negMulLog ((w i : ℝ) / W) =
          Real.negMulLog (w i : ℝ) + (w i : ℝ) * Real.log W := by
        intro i
        unfold Real.negMulLog
        rcases Nat.eq_zero_or_pos (w i) with hi | hi
        · simp [hi]
        have hwi : (0:ℝ) < w i := by exact_mod_cast hi
        rw [Real.log_div hwi.ne' hW.ne']
        field_simp
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
      unfold Real.negMulLog
      ring
    have key := mme_dwz_multinomial_entropy_polynomial_lower w 1 one_pos hpos
    simp only [Nat.cast_one, one_mul, mul_one] at key
    rw [← hWdef, ← hmass] at key
    have hmult : (Nat.multinomial Finset.univ (fun i ↦ w i) : ℝ) =
        ((W.factorial / ∏ i, (w i).factorial : ℕ) : ℝ) := by
      rw [Nat.multinomial, hWdef]
    rw [hmult] at key
    have hA : (0:ℝ) < 6 * ((W + 1 : ℕ) : ℝ) := by positivity
    have hM : (0:ℝ) < ((W.factorial / ∏ i, (w i).factorial : ℕ) : ℝ) := by
      rw [← hmult]; exact_mod_cast Nat.multinomial_pos _ _
    have hlog := Real.log_le_log (Real.exp_pos _) key
    rw [Real.log_exp, Real.log_mul (pow_pos hA _).ne' hM.ne', Real.log_pow] at hlog
    push_cast at hlog
    linarith
