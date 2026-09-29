-- Prove2me | solution 1 for lean_workbook_plus_5906
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:20.664311+00:00
-- url     : https://prove2.me/submissions/b4505b7f-3514-4ab6-a43d-679ef6e8115a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b : ℝ, a * b * (a - b) ^ 2 + 2 * (a * b - 1) * (a ^ 2 + b ^ 2) + 4 * (a * b - 2) * (a + b - 2) ≥ 0) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
