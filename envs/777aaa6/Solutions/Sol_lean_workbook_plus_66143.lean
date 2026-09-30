-- Prove2me | solution 1 for lean_workbook_plus_66143
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:25.491842+00:00
-- url     : https://prove2.me/submissions/3e1ced4f-fc80-41e1-bd47-c01a686a7f66

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h : x^2 - 4*x*y - y^2 = 5) :
  2*x^2 + 3*y^2 ≥ 5 := by
  nlinarith [sq_nonneg (x + 2*y)]
