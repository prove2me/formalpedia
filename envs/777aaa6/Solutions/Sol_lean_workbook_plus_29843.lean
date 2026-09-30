-- Prove2me | solution 1 for lean_workbook_plus_29843
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:42.762171+00:00
-- url     : https://prove2.me/submissions/9c9292f0-dd5e-4835-b6e2-4184dcbd7b5b

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^2 + y^3 ≥ x^3 + y^4) : x + y ≤ 2   := by
  have px : 0 ≤ (x - 1) ^ 2 * (x + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have py : 0 ≤ (y - 1) ^ 2 * (y ^ 2 + y + 1) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith only [h, px, py]

#print axioms solution
