-- Prove2me | solution 1 for lean_workbook_plus_54138
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:10:44.302283+00:00
-- url     : https://prove2.me/submissions/e2cc5362-a289-4c9c-80d2-0a6130ff53cc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (b + c) / a ^ 2 + (a + c) / b ^ 2 + (a + b) / c ^ 2 ≥ 2 * (1 / a + 1 / b + 1 / c)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
