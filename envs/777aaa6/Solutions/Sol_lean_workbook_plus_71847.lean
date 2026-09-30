-- Prove2me | solution 1 for lean_workbook_plus_71847
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:46.656263+00:00
-- url     : https://prove2.me/submissions/ca94ffb7-b8eb-43da-af04-a277f839c635

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≥ 2 * a * b / (a + b) := by
  have hr : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hs := Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hsum : 2 * Real.sqrt (a * b) ≤ a + b := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith [sq_nonneg (a - b)]
  apply (div_le_iff₀ (add_pos ha hb)).mpr
  have hm := mul_le_mul_of_nonneg_left hsum hr
  nlinarith

#print axioms solution
