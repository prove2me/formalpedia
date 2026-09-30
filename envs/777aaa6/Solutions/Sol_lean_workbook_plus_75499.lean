-- Prove2me | solution 1 for lean_workbook_plus_75499
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:53:35.531836+00:00
-- url     : https://prove2.me/submissions/80f2aea8-8a16-4ee7-9575-7c9bffdf5d61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (n : ℕ) (hn : 9 < n) :
    ((n - 9) / Real.sqrt 2 + 5 < (n - 1) / Real.sqrt 2 ∧
      (n - 1) / Real.sqrt 2 < (n - 8) / Real.sqrt 2 + 5 ∧
      (n - 8) / Real.sqrt 2 + 5 < n / Real.sqrt 2) ∧
      ((n - 9) / Real.sqrt 2 + 5 < n / Real.sqrt 2 - 1) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hlo : 7 < 5 * Real.sqrt 2 := by nlinarith
  have hhi : 5 * Real.sqrt 2 < 8 := by nlinarith
  have hlast : 6 * Real.sqrt 2 < 9 := by nlinarith
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
    apply (mul_lt_mul_iff_left₀ hs).mp <;>
    simp only [add_mul, sub_mul, div_mul_cancel₀ _ hs.ne', one_mul] <;>
    linarith

#print axioms solution
