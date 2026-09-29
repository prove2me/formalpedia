-- Prove2me | solution 1 for lean_workbook_plus_55163
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:03.593726+00:00
-- url     : https://prove2.me/submissions/22762cb1-e3d3-468b-903a-cd10728c7b31

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 4*(1+a*b*c) ≥ (a+1)*(b+1)*(c+1)) := by
  push_neg
  refine ⟨(3/4), ?_⟩
  refine ⟨(3), ?_⟩
  refine ⟨(1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
