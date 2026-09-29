-- Prove2me | solution 1 for lean_workbook_plus_54836
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:41.733504+00:00
-- url     : https://prove2.me/submissions/d8fd2e4c-ffc0-4b0e-ba9d-c1efc7fa5bb2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (a + b) / (a + c) / (a ^ 2 + b * c) + (b - a) ^ 2 * (c - b) ^ 2 * (a - c) ^ 2 / (b + a) / (b + c) / (b ^ 2 + a * c) + (c - a) ^ 2 * (a - b) ^ 2 * (b - c) ^ 2 / (c + a) / (c + b) / (c ^ 2 + a * b) ≥ 0) := by
  push_neg
  refine ⟨(5/2), ?_⟩
  refine ⟨(-10), ?_⟩
  refine ⟨(1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
