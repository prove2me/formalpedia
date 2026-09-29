-- Prove2me | solution 1 for lean_workbook_plus_4157
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:58:25.999894+00:00
-- url     : https://prove2.me/submissions/e925b36f-772d-4c6b-b0f7-f438cbcfaea5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y^2 + z^3 = 1) : x^2 + y^2 + z^2 ≥ 3 / 4 := by
  have hz1 : z ≤ 1 := by
    by_contra hn
    have hp : 0 < z - 1 := by linarith
    have he : 0 < (z - 1) * (z ^ 2 + z + 1) := mul_pos hp (by positivity)
    nlinarith [sq_nonneg y]
  have hpos : 0 ≤ z ^ 2 * (1 - z) := mul_nonneg (sq_nonneg z) (by linarith)
  nlinarith [sq_nonneg (x - 1 / 2)]
