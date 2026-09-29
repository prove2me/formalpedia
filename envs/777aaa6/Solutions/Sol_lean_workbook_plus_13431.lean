-- Prove2me | solution 1 for lean_workbook_plus_13431
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:35.868227+00:00
-- url     : https://prove2.me/submissions/c5a14074-4d86-4bd0-ac98-3965780b952b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x y : ℝ) (hx : x > 0) (hy : y > 0), (x + y) / (x + y + 1) > x / (x + 1) + y / (y + 1)) := by
  push_neg
  refine ⟨(1), (1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
