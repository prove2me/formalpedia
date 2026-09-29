-- Prove2me | solution 1 for lean_workbook_plus_38597
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:09.302727+00:00
-- url     : https://prove2.me/submissions/384c211a-999e-4f0b-aea5-3cf58c3878e5

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
theorem solution : ¬ (∀ a b c : ℝ, 1 = a^2 * b^3 * c^4 → a * b ≥ 1) := by
  push_neg
  refine ⟨(-2), ?_⟩
  refine ⟨(1/4), ?_⟩
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
