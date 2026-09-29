-- Prove2me | solution 1 for lean_workbook_plus_18665
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:01:30.37106+00:00
-- url     : https://prove2.me/submissions/be59f1bc-b956-4fc2-86af-cd3231264342

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a * b + b * c + c * a + a * b * c = a ^ 2 + b ^ 2 + c ^ 2 → ¬(a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
