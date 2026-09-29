-- Prove2me | solution 1 for lean_workbook_plus_6948
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:06.367412+00:00
-- url     : https://prove2.me/submissions/f0aac1d4-607a-41d7-9a39-481a3db1fd62

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e f : ℝ) (h₁ : a*2^4 + b*2^3 + c*2^2 + d*2 + e = -2) (h₂ : a + b + c + d + e = -2) (h₃ : a*(-1)^4 + b*(-1)^3 + c*(-1)^2 + d*(-1) + e = -2) (h₄ : a*(-2)^4 + b*(-2)^3 + c*(-2)^2 + d*(-2) + e = 14) (h₅ : a*3^4 + b*3^3 + c*3^2 + d*3 + e = 14) : a*0^4 + b*0^3 + c*0^2 + d*0 + e = -2 := by
  (intros; linarith)
