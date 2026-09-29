-- Prove2me | solution 1 for lean_workbook_plus_69849
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:11.149193+00:00
-- url     : https://prove2.me/submissions/5f507a62-85be-49a3-9385-09034c170950

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : ‖a + (b - 3) * Complex.I‖ = 3) : a^2 + (b-3)^2 = 9 := by
  have hh := congrArg (fun t : ℝ => t ^ 2) h₁
  norm_num [Complex.sq_norm, Complex.normSq_apply] at hh
  simpa only [pow_two] using hh
