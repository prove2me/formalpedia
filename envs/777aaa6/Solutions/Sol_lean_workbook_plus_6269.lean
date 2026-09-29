-- Prove2me | solution 1 for lean_workbook_plus_6269
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:38.21672+00:00
-- url     : https://prove2.me/submissions/d0b3fd3d-94e9-489f-9e1a-b86fe4a07cde

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ b c : ℝ, 2 * b * c + 2 * b^2 + 2 * c^2 ≤ 6 + b^3 * c + b * c^3) := by
  push_neg
  refine ⟨(2), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
