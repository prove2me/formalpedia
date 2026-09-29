-- Prove2me | solution 1 for lean_workbook_plus_63584
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:33:13.873276+00:00
-- url     : https://prove2.me/submissions/59401c63-524a-4e3b-912b-d0a1ae4ac3f5

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x1 x2 : ℝ, x1 + x2 ≤ 2 * Real.sqrt (x1 * x2 + 1) ∧ 2 * Real.sqrt (x1 * x2 + 1) ≤ x1 + x2 + 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
