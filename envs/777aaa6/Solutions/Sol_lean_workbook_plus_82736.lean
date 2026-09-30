-- Prove2me | solution 1 for lean_workbook_plus_82736
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:49:41.145131+00:00
-- url     : https://prove2.me/submissions/d75cd69a-22eb-49ad-98f8-7954b461df75

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : √(3 + 2 * Real.sqrt 2) = √2 + 1 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity) |>.mpr
  nlinarith

#print axioms solution
