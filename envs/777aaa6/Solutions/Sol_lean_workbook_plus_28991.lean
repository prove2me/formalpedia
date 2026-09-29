-- Prove2me | solution 1 for lean_workbook_plus_28991
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:38:10.153467+00:00
-- url     : https://prove2.me/submissions/7f00094a-aec0-4d74-b2b8-5b03e5b6f4d2

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a + b + c > 0 → 3 / 2 + a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≥ a * b + b * c + c * a) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
