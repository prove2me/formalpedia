-- Prove2me | solution 1 for lean_workbook_plus_28605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:58.370431+00:00
-- url     : https://prove2.me/submissions/dbafe4ff-76c4-4475-a9e2-2c1b45c3789d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, x^2 + y^2 - 1 < x * y → x + y - |x - y| < 2 := by
  intro x y h
  by_cases hxy : x≤y
  · have hp := mul_nonneg (show 0≤y-x by linarith) (show 0≤y-x by linarith)
    have hx : x<1 := by
      by_contra hn
      have hp := mul_nonneg (show 0≤y by linarith) (show 0≤y-x by linarith)
      nlinarith [sq_nonneg (x-1)]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · have hy : y<1 := by
      by_contra hn
      have hp := mul_nonneg (show 0≤x by linarith) (show 0≤x-y by linarith)
      nlinarith [sq_nonneg (y-1)]
    rw [abs_of_nonneg (by linarith : 0≤x-y)]
    linarith
