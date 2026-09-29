-- Prove2me | solution 1 for lean_workbook_plus_55974
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:08.126245+00:00
-- url     : https://prove2.me/submissions/184ee924-03b5-4987-b9c6-6b1852e293df

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, x + y + z ≥ 2 → (1 - x) / x * (1 - y) / y * (1 - z) / z ≤ 1 / 8) := by
  push_neg
  refine ⟨(10), ?_⟩
  refine ⟨(1/2), ?_⟩
  refine ⟨(2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
