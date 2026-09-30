-- Prove2me | solution 1 for lean_workbook_plus_32732
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:40.501001+00:00
-- url     : https://prove2.me/submissions/f5d3d8fc-2c9e-47c2-97df-ed1416d2193e

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 1 < x ∧ x < 3) (hy : 1 < y ∧ y < 3) : |(x - 2) * (y - 2)| < 1   := by
  apply abs_lt.mpr
  constructor <;> nlinarith

#print axioms solution
