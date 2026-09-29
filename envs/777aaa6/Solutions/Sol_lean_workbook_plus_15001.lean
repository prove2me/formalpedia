-- Prove2me | solution 1 for lean_workbook_plus_15001
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T15:59:07.301636+00:00
-- url     : https://prove2.me/submissions/45d4aaaa-6ce3-46ce-8856-639708bbb99b

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c d : ℝ, (a + b + c + d)^4 + 16 * (a - b) * (b - c) * (c - d) * (d - a) - 4 * (a + b + c + d)^2 * (c + a) * (b + d) ≥ 0) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 1 , ?_⟩
  norm_num
  refine ⟨ 2 , ?_⟩
  norm_num
  refine ⟨ -  1 , ?_⟩
  norm_num
