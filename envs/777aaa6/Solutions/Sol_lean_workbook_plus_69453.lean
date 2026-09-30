-- Prove2me | solution 1 for lean_workbook_plus_69453
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:00.067629+00:00
-- url     : https://prove2.me/submissions/45cd5a0c-1e6b-4ae3-91d8-d41847f5c6cc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) : (Real.sqrt 18 - Real.sqrt 8) / Real.sqrt 2 = 1 := by
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h18 : Real.sqrt 18 = 3 * Real.sqrt 2 := by
    apply Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity) |>.mpr
    nlinarith
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    apply Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity) |>.mpr
    nlinarith
  rw [h18, h8, show 3 * Real.sqrt 2 - 2 * Real.sqrt 2 = Real.sqrt 2 by ring]
  exact div_self hp.ne'

#print axioms solution
