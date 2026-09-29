-- Prove2me | solution 1 for lean_workbook_plus_16187
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:52.05029+00:00
-- url     : https://prove2.me/submissions/9993b3de-7f4c-4ced-a3db-b2fed1bda1f7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) : ℝ) ≤ 1) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
