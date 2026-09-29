-- Prove2me | solution 1 for lean_workbook_plus_63038
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:31.983731+00:00
-- url     : https://prove2.me/submissions/1199f954-c057-4336-9326-468fef35c91f

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
theorem solution : ¬ (∀ (x y z t : ℝ) (hx : x < 0) (hy : y < 0) (hz : z < 0) (ht : t < 0), (t + y - 1) * (x + z - 1) ≤ 0) := by
  push_neg
  refine ⟨(-1), ?_⟩
  refine ⟨(-1), ?_⟩
  refine ⟨(-1), ?_⟩
  refine ⟨(-1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
