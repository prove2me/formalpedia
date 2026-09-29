-- Prove2me | solution 1 for lean_workbook_plus_14146
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:10.22907+00:00
-- url     : https://prove2.me/submissions/21d34f69-5a7d-4c91-b5d1-9101940b1f10

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (a + 1) ^ 2 + 1 / (b + 1) ^ 2 + 1 / (c + 1) ^ 2 + (a * b + b * c + c * a) / 8) ≥ 9 / 8) := by
  push_neg
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
