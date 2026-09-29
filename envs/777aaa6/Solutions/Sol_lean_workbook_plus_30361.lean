-- Prove2me | solution 1 for lean_workbook_plus_30361
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:09.620345+00:00
-- url     : https://prove2.me/submissions/aa94fdbd-50b6-4440-8101-c7cdc65dc403

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (a^7 + b^7 + c) * (1 / a^3 + 1 / b^3 + c^3) ≥ (a^2 + b^2 + c^2)^2) := by
  push_neg
  refine ⟨(-1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(-3/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
