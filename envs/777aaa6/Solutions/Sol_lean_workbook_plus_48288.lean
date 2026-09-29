-- Prove2me | solution 1 for lean_workbook_plus_48288
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:31.311667+00:00
-- url     : https://prove2.me/submissions/a2ae2547-09e6-4154-91f8-ea27a069da07

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p q : ℝ, p^2 - 6 * p + q^2 - 2 * q + 6 ≥ p^2 - 6 * p + 9) := by
  push_neg
  refine ⟨(0), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
