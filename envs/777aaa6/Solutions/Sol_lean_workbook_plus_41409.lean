-- Prove2me | solution 1 for lean_workbook_plus_41409
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:43.175694+00:00
-- url     : https://prove2.me/submissions/377cdb86-a9c1-4ade-84ac-fd6ba9c3123d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : (x - 1/x) + (y - 1/y) ≤ (x*y - 1/(x*y)) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hxy : 0 ≤ x*y-1 := by nlinarith [mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ y-1 by linarith)]
  have hi : (x*y-1/(x*y))-((x-1/x)+(y-1/y)) = (x-1)*(y-1)*(x*y-1)/(x*y) := by
    field_simp
    ring
  have hn : 0 ≤ (x-1)*(y-1)*(x*y-1)/(x*y) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hxy) (by positivity)
  linarith
