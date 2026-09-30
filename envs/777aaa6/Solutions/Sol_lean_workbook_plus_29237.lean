-- Prove2me | solution 1 for lean_workbook_plus_29237
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:08.17071+00:00
-- url     : https://prove2.me/submissions/5c98717b-e368-42fc-8838-627960d8b008

import Mathlib
set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (hx : x = a - b) (hy : y = b - c) (hz : z = c - a) : a^3 * x^2 * z^2 + b^3 * x^2 * y^2 + c^3 * y^2 * z^2 - (a + b + c) * x^2 * y^2 * z^2 = (a * x * z + b * x * y + c * y * z) * (a^2 * x * z + b^2 * x * y + c^2 * y * z)   := by
  rw [hx,hy,hz]
  ring

#print axioms solution
