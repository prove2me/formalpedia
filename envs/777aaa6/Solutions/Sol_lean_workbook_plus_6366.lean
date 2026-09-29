-- Prove2me | solution 1 for lean_workbook_plus_6366
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:05.537792+00:00
-- url     : https://prove2.me/submissions/42a1e91b-99d5-4b15-bc96-9f5b4ccca892

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^3 + y^3) / (x^2 + x * y + y^2) - (x + y) / 3 = 2 * (x + y) * (x - y)^2 / (3 * (x^2 + x * y + y^2)) ∧ 2 * (x + y) * (x - y)^2 / (3 * (x^2 + x * y + y^2)) >= 0 := by
  have hd : x^2+x*y+y^2 ≠ 0 := ne_of_gt (by positivity)
  constructor
  · field_simp
    <;> ring
  · positivity
