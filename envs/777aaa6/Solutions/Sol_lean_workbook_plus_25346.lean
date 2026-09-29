-- Prove2me | solution 1 for lean_workbook_plus_25346
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:48.197052+00:00
-- url     : https://prove2.me/submissions/a9fa257f-5456-4980-87e6-19297ae5d9d9

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
theorem solution : ¬ (∀ a b : ℝ, a * b * (a ^ 4 + b ^ 4) + 2 * a * b ≥ 2 * a * b * (a ^ 2 + b ^ 2)) := by
  push_neg
  refine ⟨(-3), ?_⟩
  refine ⟨(5/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
