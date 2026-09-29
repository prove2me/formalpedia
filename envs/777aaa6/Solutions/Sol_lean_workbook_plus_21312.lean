-- Prove2me | solution 1 for lean_workbook_plus_21312
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:13.890391+00:00
-- url     : https://prove2.me/submissions/e4836402-47ed-4336-87b0-26bff9f3df27

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℤ, (a - b) * (b - c) * (c - a) = (b - c) * (c - a) + (c - a) * (a - b) + (a - b) * (b - c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
