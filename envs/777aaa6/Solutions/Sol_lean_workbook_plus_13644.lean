-- Prove2me | solution 1 for lean_workbook_plus_13644
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:23.753556+00:00
-- url     : https://prove2.me/submissions/cfb75290-45e6-4a43-8931-5432b751f640

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ p q x : ℝ, p^2*q - 2*p*q*x + q*x^2 ≥ -p^2*q + 2*p*q*x - q*x^2) := by
  push_neg
  refine ⟨(3/4), ?_⟩
  refine ⟨(-2/3), ?_⟩
  refine ⟨(0), ?_⟩
  norm_num [Real.sqrt_eq_zero_of_nonpos, Real.sqrt_le_iff, Real.sqrt_lt', Real.lt_sqrt]
