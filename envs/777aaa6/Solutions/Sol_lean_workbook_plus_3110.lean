-- Prove2me | solution 1 for lean_workbook_plus_3110
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:33.938563+00:00
-- url     : https://prove2.me/submissions/891c3600-b3ca-47b7-8695-80068c089890

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x y : ℝ) (h1 : 0 < x ∧ 0 < y) (h2 : x^3 + y^3 = x - y) : x^2 + y^2 < 1 := by
  rcases h1 with ⟨hx, hy⟩
  have hxy : y < x := by nlinarith [pow_pos hx 3, pow_pos hy 3]
  have hx1 : x < 1 := by
    by_contra hh
    have hmul := mul_nonneg (show 0 ≤ x-1 by linarith) (show 0 ≤ x^2+x by positivity)
    nlinarith [pow_pos hy 3]
  have hx2 : x^2 < 1 := by nlinarith [sq_nonneg (x-1)]
  have hmul : x*y < 1 := lt_trans (mul_lt_mul_of_pos_left hxy hx) (by nlinarith [hx2])
  have hp : 0 < y*(2-x^2-x*y) := mul_pos hy (by linarith)
  have hid : (x+y)*(1-x^2-y^2) = y*(2-x^2-x*y) := by
    linear_combination -h2
  have hs : 0 < x+y := by positivity
  by_contra hh
  have hprod := mul_nonneg (le_of_lt hs) (show 0 ≤ x^2+y^2-1 by linarith)
  nlinarith [hprod]
