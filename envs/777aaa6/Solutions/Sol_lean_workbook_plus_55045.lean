-- Prove2me | solution 1 for lean_workbook_plus_55045
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:56.276047+00:00
-- url     : https://prove2.me/submissions/031d52cc-c1e5-462d-bb62-859565496fcb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c x y z : ℝ, a ≥ x ∧ b ≥ y ∧ c ≥ z → 0 ≤ a * (b + c) / (x * (y + z)) + b * (c + a) / (y * (z + x)) + c * (a + b) / (z * (x + y)) - a / x - b / y - c / z) := by
  push_neg
  refine ⟨(3/2), (1/2), (3/4), (-10), (1/3), (1/4), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
