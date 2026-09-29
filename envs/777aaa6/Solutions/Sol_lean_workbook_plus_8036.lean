-- Prove2me | solution 1 for lean_workbook_plus_8036
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:13.593745+00:00
-- url     : https://prove2.me/submissions/3cdeb0ca-5a40-4b54-9684-3d6843c80f01

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (x^2 - 2 * x + 2) / (3 * x^2 - 10 * x + 6) + 3 * x / (x^2 + 2) = 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
