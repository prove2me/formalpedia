-- Prove2me | solution 1 for lean_workbook_plus_77674
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:39.542579+00:00
-- url     : https://prove2.me/submissions/4daf5f8b-2d98-46e5-b8ca-9409ce7256c6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ¬ (∀ a b c : ℝ,
    a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 →
    a ^ 4 / Real.sqrt (b ^ 3 + 7) + b ^ 4 / Real.sqrt (c ^ 3 + 7) +
      c ^ 4 / Real.sqrt (a ^ 3 + 7) ≥ 3 / 2) := by
  intro h
  have hh := h 1 1 1 (by norm_num)
  have hi : 1 / Real.sqrt (8 : ℝ) + 1 / Real.sqrt 8 + 1 / Real.sqrt 8 =
      3 / Real.sqrt 8 := by ring
  have hn : (1 : ℝ) + 7 = 8 := by norm_num
  have hbound : (3 : ℝ) / 2 ≤ 3 / Real.sqrt 8 := by
    simpa only [one_pow, hn, hi] using hh
  have hp : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hm := (le_div_iff₀ hp).mp hbound
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num)
  nlinarith

#print axioms solution
