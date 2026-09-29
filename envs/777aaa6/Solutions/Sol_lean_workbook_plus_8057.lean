-- Prove2me | solution 1 for lean_workbook_plus_8057
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:21.038701+00:00
-- url     : https://prove2.me/submissions/bddf08b4-d3ad-458f-a9c4-43a5709938ca

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 2 * a * b + 2 * b * c + 2 * a * c ≥ (b + c - a) * (a + b) * (c + a) / (b + c) + (a + c - b) * (b + c) * (a + b) / (c + a) + (a + b - c) * (c + a) * (b + c) / (a + b)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  2 , ?_⟩
  norm_num at *
