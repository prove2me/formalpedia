-- Prove2me | solution 1 for lean_workbook_plus_21583
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:36.252016+00:00
-- url     : https://prove2.me/submissions/1bc613f6-ecd1-4eb9-b219-a473b9fbe6a9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x^2 + y^2 + z^2 ≥ (3 - x - y - z) / 2) := by
  push_neg
  refine ⟨(0), (0), (0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
