-- Prove2me | solution 1 for lean_workbook_plus_6211
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:46.056931+00:00
-- url     : https://prove2.me/submissions/d1e46aab-590b-4e3d-b7d5-43212575117b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (1 + b * c) + b / (1 + c * a) + c / (1 + a * b) + a * b * c ≤ 5 / 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
