-- Prove2me | solution 1 for lean_workbook_plus_43384
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T15:59:24.862855+00:00
-- url     : https://prove2.me/submissions/95055903-d0d0-476a-b2eb-bf538d50fd5e

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ 2)) := by
  push_neg
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 0 , ?_⟩
  norm_num
  refine ⟨ 3 , ?_⟩
  norm_num
