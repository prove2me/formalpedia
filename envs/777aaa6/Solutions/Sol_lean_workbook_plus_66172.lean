-- Prove2me | solution 1 for lean_workbook_plus_66172
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:17.524251+00:00
-- url     : https://prove2.me/submissions/deb217d2-236d-4c16-a850-c721ef22ed5d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a ≥ b ∧ b ≥ 1 ∧ 1 ≥ c → a * b ≤ 2 - c ∧ (b ^ 2 - 1) * (1 - c) ≥ 0 ∧ (a - 1) * (1 - c) ≥ 0) := by
  push_neg
  refine ⟨(10), (4), (-10), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
