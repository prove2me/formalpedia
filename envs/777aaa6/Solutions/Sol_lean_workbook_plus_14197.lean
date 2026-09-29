-- Prove2me | solution 1 for lean_workbook_plus_14197
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:45:13.585373+00:00
-- url     : https://prove2.me/submissions/1839926f-73b8-4f7c-a70d-8f6302a48cd2

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (b * c + 1) + b / (c * a + 1) + c / (a * b + 1) + a * b * c ≤ 5 / 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 3 , ?_⟩
  norm_num at *
