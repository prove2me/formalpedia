-- Prove2me | solution 1 for lean_workbook_plus_78672
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:40:33.983899+00:00
-- url     : https://prove2.me/submissions/4474b284-91c4-41a3-bef3-aac8e2046d01

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, a^2 / (a + 2) ≤ a / 3) := by
  push_neg
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
