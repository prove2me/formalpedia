-- Prove2me | solution 1 for lean_workbook_plus_69751
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:01.109215+00:00
-- url     : https://prove2.me/submissions/adbb9e89-fc88-4468-90d6-2527027a825f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d e f : ℝ) :
  (a^2+b^2+c^2)*(d^2+e^2+f^2) ≥ (a*d+b*e+c*f)^2 := by
  nlinarith only [sq_nonneg (a * e - b * d), sq_nonneg (a * f - c * d),
    sq_nonneg (b * f - c * e)]
