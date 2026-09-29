-- Prove2me | solution 1 for lean_workbook_plus_23128
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:00.629492+00:00
-- url     : https://prove2.me/submissions/b11e97ce-c639-40a4-be57-6415a4c94b15

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ x y z : ℝ, (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) + (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) ≤ 3) := by
  push_neg
  refine ⟨(2/3), ?_⟩
  refine ⟨(1/4), ?_⟩
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
