-- Prove2me | solution 1 for lean_workbook_plus_37797
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:16.844825+00:00
-- url     : https://prove2.me/submissions/985a772d-70a6-41d7-b97d-688d1383a0ac

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, (3 / (2 * a * b * c) ≥ 81 / (2 * (a + b + c) ^ 3))) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
