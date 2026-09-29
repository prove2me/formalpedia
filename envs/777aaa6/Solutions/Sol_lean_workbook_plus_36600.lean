-- Prove2me | solution 1 for lean_workbook_plus_36600
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:48.690596+00:00
-- url     : https://prove2.me/submissions/19b357f2-9ee9-4db4-aa24-3be57d28c124

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
theorem solution : ¬ (∀ (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1), -2 * x ^ 2 + 2 * x + 2 ≤ 5 / 4) := by
  push_neg
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
