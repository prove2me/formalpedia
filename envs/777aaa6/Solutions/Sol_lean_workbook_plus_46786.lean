-- Prove2me | solution 1 for lean_workbook_plus_46786
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:40.750545+00:00
-- url     : https://prove2.me/submissions/f082d633-61c1-43cb-9567-538c55576120

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b + b * c + c * a = 1 → a ^ 2 / b + b ^ 2 / c + c ^ 2 / a - 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a + b + c - 2) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
