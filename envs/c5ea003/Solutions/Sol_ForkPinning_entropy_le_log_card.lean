-- Prove2me | solution 1 for ForkPinning.entropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:10:53.844978+00:00
-- url     : https://prove2.me/submissions/89d1f135-5bdc-4c60-8adc-b9984e877426

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (X : Ω → κ) : H X ≤ Real.log (Fintype.card κ) := by
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnnX : ∀ k : κ, 0 ≤ prb X k := by
    intro k
    unfold prb
    positivity
  have hsumX : ∑ k : κ, prb X k = 1 := by
    simp only [prb, fiber]
    rw [← Finset.sum_div, div_eq_one_iff_eq hΩ, ← Nat.cast_sum]
    congr 1
    rw [← Finset.card_univ (α := Ω)]
    exact (Finset.card_eq_sum_card_fiberwise
      (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hne : Nonempty κ := ⟨X (Classical.arbitrary Ω)⟩
  have hn : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    have := Fintype.card_pos (α := κ)
    exact_mod_cast this
  have hmul_log : ∀ t : ℝ, 0 ≤ t → t - 1 ≤ t * Real.log t := by
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0]
      simp
    · have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / t by positivity)
      rw [Real.log_div one_ne_zero (ne_of_gt h0), Real.log_one] at h1
      have h2 : 1 - 1 / t ≤ Real.log t := by linarith
      calc t - 1 = t * (1 - 1 / t) := by field_simp
        _ ≤ t * Real.log t := mul_le_mul_of_nonneg_left h2 ht
  have htangent : ∀ p : ℝ, 0 ≤ p →
      Real.negMulLog p ≤ p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ) := by
    intro p hp
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · rw [← hp0]
      simp [Real.negMulLog]
    · have ht := hmul_log (p * (Fintype.card κ : ℝ)) (by positivity)
      rw [Real.log_mul (ne_of_gt hp0) (ne_of_gt hn)] at ht
      unfold Real.negMulLog
      have hfinal : 0 ≤ p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ)
          - (-p * Real.log p) := by
        have key : p * Real.log (Fintype.card κ) - p + 1 / (Fintype.card κ : ℝ)
            - (-p * Real.log p)
            = (p * (Fintype.card κ : ℝ) * (Real.log p + Real.log (Fintype.card κ : ℝ))
                - (p * (Fintype.card κ : ℝ) - 1)) / (Fintype.card κ : ℝ) := by
          field_simp
          ring
        rw [key]
        apply div_nonneg _ (le_of_lt hn)
        linarith [ht]
      linarith [hfinal]
  calc H X = ∑ k : κ, Real.negMulLog (prb X k) := rfl
    _ ≤ ∑ k : κ, (prb X k * Real.log (Fintype.card κ) - prb X k
          + 1 / (Fintype.card κ : ℝ)) :=
        Finset.sum_le_sum (fun k _ => htangent (prb X k) (hnnX k))
    _ = Real.log (Fintype.card κ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumX,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
        ring
