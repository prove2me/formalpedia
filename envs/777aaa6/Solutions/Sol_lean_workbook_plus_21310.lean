-- Prove2me | solution 1 for lean_workbook_plus_21310
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:00.377586+00:00
-- url     : https://prove2.me/submissions/01a7992c-aa89-4e46-92d7-002f9b409d10

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, 1 ≥ a ^ 2 + b ^ 2 + c ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
