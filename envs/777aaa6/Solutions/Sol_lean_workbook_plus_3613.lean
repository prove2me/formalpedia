-- Prove2me | solution 1 for lean_workbook_plus_3613
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:23.829351+00:00
-- url     : https://prove2.me/submissions/45cd728e-17f8-483a-815b-13493a38782b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (x + y + z) * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) ≥ x * y * z * (x + y + z) ^ 2) := by
  push_neg
  refine ⟨(-1), ?_⟩
  refine ⟨(-4), ?_⟩
  refine ⟨(1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
