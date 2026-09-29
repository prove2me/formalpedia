-- Prove2me | solution 1 for lean_workbook_plus_36047
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:14.913792+00:00
-- url     : https://prove2.me/submissions/ad1eec5b-8c39-4e67-9970-958278d90904

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → (a + b) / (c * Real.sqrt (a ^ 2 + b ^ 2)) + (b + c) / (a * Real.sqrt (b ^ 2 + c ^ 2)) + (c + a) / (b * Real.sqrt (c ^ 2 + a ^ 2)) ≥ 3 * Real.sqrt 6 / Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
