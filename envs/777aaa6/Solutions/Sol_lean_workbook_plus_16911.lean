-- Prove2me | solution 1 for lean_workbook_plus_16911
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:42.66169+00:00
-- url     : https://prove2.me/submissions/f544b30a-496f-40ec-9d09-3c44fef4fcfe

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ u v w : ℝ, u < (Real.sqrt 3) - 1 ∧ v < (Real.sqrt 3) - 1 ∧ w < (Real.sqrt 3) - 1 → 3 * v ^ 2 + w ^ 3 < 2) := by
  push_neg
  refine ⟨(-1), (-1), (-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
  all_goals first | positivity | linarith
