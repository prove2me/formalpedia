-- Prove2me | solution 1 for lean_workbook_plus_23023
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:16.5726+00:00
-- url     : https://prove2.me/submissions/6cf1ddf3-b0cf-4239-8b37-0ab778183a6c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a+b+c)^2 ≥ 3*(a^2+b^2+c^2)) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
