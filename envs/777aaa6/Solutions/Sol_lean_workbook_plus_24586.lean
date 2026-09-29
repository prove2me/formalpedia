-- Prove2me | solution 1 for lean_workbook_plus_24586
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:42.647762+00:00
-- url     : https://prove2.me/submissions/ef25f5cf-0e35-4f44-9ffd-3dff7b15a829

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c ≤ 3), 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 3) := by
  push_neg
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  refine ⟨(1), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
