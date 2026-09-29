-- Prove2me | solution 1 for lean_workbook_plus_43029
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:49.035673+00:00
-- url     : https://prove2.me/submissions/0f6f8b31-d43c-40a7-9e9a-50de3ab86b22

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x : ℝ, (18 - x ^ 2) / 2 ≥ (6 - x) ^ 2 / 4) := by
  push_neg
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
