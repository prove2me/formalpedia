-- Prove2me | solution 1 for lean_workbook_plus_45671
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:12:59.843324+00:00
-- url     : https://prove2.me/submissions/e853cb3e-9c16-43a7-8b23-a24f190b6b56

import Mathlib
set_option autoImplicit false

theorem solution {a b : ℝ} (hab : a > b) (hb : b > 0) : Real.sqrt a > Real.sqrt b   := by
  exact Real.sqrt_lt_sqrt (by positivity) hab

#print axioms solution
