-- Prove2me | solution 1 for lean_workbook_plus_19348
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:11:25.520727+00:00
-- url     : https://prove2.me/submissions/3606bcf5-3d34-4803-b643-b52625578409

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p : ℝ, p > 0 ∧ p ≠ 1 → 1 / 27 * ((9 - p) / 2) ^ 2 ≤ 1 / p) := by
  push_neg
  refine ⟨(27), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
