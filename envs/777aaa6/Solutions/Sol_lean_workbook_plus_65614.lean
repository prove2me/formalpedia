-- Prove2me | solution 1 for lean_workbook_plus_65614
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:42.713502+00:00
-- url     : https://prove2.me/submissions/3bd9751b-4a4e-44f0-b281-6138f61d08bf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 3) : 1 + 2 * Real.sqrt x ≥ x := by
  by_cases h : x ≤ 1
  · linarith [Real.sqrt_nonneg x]
  · have hs : 1 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
    linarith [hx.2]

#print axioms solution
