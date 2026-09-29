-- Prove2me | solution 1 for lean_workbook_plus_19557
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:55.658223+00:00
-- url     : https://prove2.me/submissions/ceb1d68b-c442-4cfb-8aaf-40b6ed9ef3be

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ∈ Set.Icc 0 (1 / 2) ∧ b ∈ Set.Icc 0 (1 / 2) ∧ c ∈ Set.Icc 0 (1 / 2) → a * (1 - a) + b * (1 - b) + c * (1 - c) ≤ 2 / 3) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
