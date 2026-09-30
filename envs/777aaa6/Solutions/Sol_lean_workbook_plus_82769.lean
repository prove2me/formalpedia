-- Prove2me | solution 1 for lean_workbook_plus_82769
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:24.245159+00:00
-- url     : https://prove2.me/submissions/e092f2a9-b7d7-4faa-9fec-bb7ac534f701

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem rational_bounds (a : ℝ) (ha : a ^ 3 - a - 2 = 0) : 3 / 2 < a ∧ a < 2 := by
  have hn : -1 < a := by
    by_contra hn
    have hle : a ≤ -1 := le_of_not_gt hn
    have hs : 0 ≤ a ^ 2 - 1 := by nlinarith [sq_nonneg (a + 1)]
    have := mul_nonpos_of_nonpos_of_nonneg (show a ≤ 0 by linarith) hs
    nlinarith
  have hp : 0 < a := by
    by_contra hp
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hp) (sq_nonneg a)
    nlinarith
  constructor
  · by_contra h
    have hle : a ≤ 3 / 2 := le_of_not_gt h
    have hf : 0 ≤ a ^ 2 + (3 / 2) * a + 5 / 4 := by positivity
    have := mul_nonneg (show 0 ≤ 3 / 2 - a by linarith) hf
    nlinarith
  · by_contra h
    have hle : 2 ≤ a := le_of_not_gt h
    have hf : 0 ≤ a ^ 2 + 2 * a + 3 := by positivity
    have := mul_nonneg (show 0 ≤ a - 2 by linarith) hf
    nlinarith

theorem real_fourth_root_bounds (a : ℝ) (ha : a ^ 3 - a - 2 = 0) :
    (5 : ℝ) ^ (1 / 4 : ℝ) < a ∧ a < 2 := by
  obtain ⟨hl, hu⟩ := rational_bounds a ha
  have hp : 0 ≤ a := by linarith
  refine ⟨?_, hu⟩
  apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg (by norm_num) _) hp
    (show (0 : ℝ) < 4 by norm_num)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
  rw [show (1 / 4 : ℝ) * 4 = 1 by ring, Real.rpow_one, Real.rpow_ofNat]
  have h4 := pow_lt_pow_left₀ hl (by norm_num : (0 : ℝ) ≤ 3 / 2) (by decide : (4 : ℕ) ≠ 0)
  nlinarith

theorem solution (a : ℝ) (ha : a ^ 3 - a - 2 = 0) :
    (5 : ℝ) ^ (1 / 4) < a ∧ a < 2 := by
  obtain ⟨hl, hu⟩ := rational_bounds a ha
  norm_num only [Nat.reduceDiv, pow_zero]
  exact ⟨by linarith, hu⟩

#print axioms rational_bounds
#print axioms real_fourth_root_bounds
#print axioms solution
