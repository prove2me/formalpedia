-- Prove2me | solution 1 for lean_workbook_plus_17061
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:48.144603+00:00
-- url     : https://prove2.me/submissions/7025caea-9f3a-44d3-8cb6-949d5b01c9a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) : (a+b+c+d+e)*(c^2+a^2+b^2+d^2+e^2) - 5*a*b*c - 5*b*c*d - 5*c*d*e - 5*a*d*e - 5*a*b*e = (e-a)^2*(2*b+3/4*d) + (d-e)^2*(2*a+3/4*c) + (c-d)^2*(2*e+3/4*b) + (b-c)^2*(2*d+3/4*a) + (a-b)^2*(2*c+3/4*e) + 1/4*(2*c-d-e)^2*c + 1/4*(2*d-e-a)^2*d + 1/4*(2*e-a-b)^2*e + 1/4*(2*b-c-d)^2*b + 1/4*(2*a-b-c)^2*a := by
  (intros; linarith)
