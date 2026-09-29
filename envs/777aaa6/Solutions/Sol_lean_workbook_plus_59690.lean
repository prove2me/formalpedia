-- Prove2me | solution 1 for lean_workbook_plus_59690
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T18:19:53.743593+00:00
-- url     : https://prove2.me/submissions/58ade485-7b4a-4562-acaa-7ecfc9dbd921

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
theorem solution : ¬ (∀ a b c : ℝ, (a^2 + b^2 + c^2 - a * b - b * c - c * a) * (1 / (a^2 + b^2 + c^2) - (a + b + c) / (3 * (a^3 + b^3 + c^3))) ≥ 0) := by
  push_neg
  refine ⟨(5/2), ?_⟩
  refine ⟨(-4), ?_⟩
  refine ⟨(4), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
