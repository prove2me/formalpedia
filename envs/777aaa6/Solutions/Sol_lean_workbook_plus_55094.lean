-- Prove2me | solution 1 for lean_workbook_plus_55094
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:13:23.530203+00:00
-- url     : https://prove2.me/submissions/6221a3fa-1bb4-4e25-80bb-6e8d57c656c1

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 7 / 3 → (a * b + b * c + c * a + a * b * c) * (1 / (a + b) ^ 3 + 1 / (b + c) ^ 3 + 1 / (c + a) ^ 3) ≥ 51 / 28) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
