-- Prove2me | solution 1 for lean_workbook_plus_8379
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:11.833382+00:00
-- url     : https://prove2.me/submissions/3883d808-54f1-4cbe-95ad-b040d7d4a4b0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ t : ℝ, 2 * (t + 1) * (t ^ 2 - t + 1) / (t ^ 2 + 1) ≥ (t + 1)) := by
  push_neg
  refine ⟨(-2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
