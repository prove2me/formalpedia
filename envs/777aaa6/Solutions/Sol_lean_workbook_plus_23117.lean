-- Prove2me | solution 1 for lean_workbook_plus_23117
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:20.292523+00:00
-- url     : https://prove2.me/submissions/e867af6b-a87c-41ce-9c6a-dd769bdde951

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x * (y + z) + y * (x + z) + z * (x + y) + 8 * x * y * z / (x + y + z) ≥ 5 * (x + y) * (y + z) * (z + x) / (x + y + z)) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
