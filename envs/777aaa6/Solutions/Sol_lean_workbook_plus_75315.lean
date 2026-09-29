-- Prove2me | solution 1 for lean_workbook_plus_75315
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:14:19.141628+00:00
-- url     : https://prove2.me/submissions/580d65a8-75c6-4f08-a345-b8bda1ce447f

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∃ f : ℚ → ℚ, ∀ x y : ℚ, abs (f x - f y) > 1) := by
  push_neg
  norm_num at *
  intro
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
