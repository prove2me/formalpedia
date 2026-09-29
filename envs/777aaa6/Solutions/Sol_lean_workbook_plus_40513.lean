-- Prove2me | solution 1 for lean_workbook_plus_40513
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:58.762199+00:00
-- url     : https://prove2.me/submissions/75d0f44d-4872-43ca-94e6-166edf649e43

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a : ℝ, 4 * (a ^ 2 + a + 1) ^ 2 * (a ^ 3 + 3 * a + 2) ≥ (a ^ 2 + 1) * (a + 1) ^ 2 * (a + 2) ^ 3) := by
  push_neg
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
