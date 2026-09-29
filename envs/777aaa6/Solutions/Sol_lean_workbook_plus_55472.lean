-- Prove2me | solution 1 for lean_workbook_plus_55472
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:30:14.303423+00:00
-- url     : https://prove2.me/submissions/2f09fb20-e74f-4c50-bd0b-458b00815a48

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (¬∃ (x y : ℚ), x^4 = 2*y^2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
