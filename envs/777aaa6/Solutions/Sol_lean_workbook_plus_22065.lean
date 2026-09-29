-- Prove2me | solution 1 for lean_workbook_plus_22065
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:13.495378+00:00
-- url     : https://prove2.me/submissions/7126f93b-99ad-4fb3-96e6-2747de23d1c1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 4) : Real.sqrt x ≥ x / 2 := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg x]
