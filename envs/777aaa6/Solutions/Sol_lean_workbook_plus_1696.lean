-- Prove2me | solution 1 for lean_workbook_plus_1696
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:15.739409+00:00
-- url     : https://prove2.me/submissions/2739bdde-a547-4d51-99fe-0463b1e67130

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1), (1 + a) * (1 + b) * (1 + c) ≥ 2 * (1 + a + b + c)) := by
  push_neg
  refine ⟨(1/2), ?_⟩
  refine ⟨(1/2), ?_⟩
  refine ⟨(1/2), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
