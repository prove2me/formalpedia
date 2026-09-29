-- Prove2me | solution 1 for lean_workbook_plus_65349
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:10.28167+00:00
-- url     : https://prove2.me/submissions/5d2c2cd7-b449-438e-86d8-77ce4bb5e68d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (D t : ℝ) (h₁ : D = 45 * t) (h₂ : D - 3 = 36 * (t - 1/20)), t = 3/4 ∧ D = 33/4) := by
  push_neg
  refine ⟨(6), (2/15), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
