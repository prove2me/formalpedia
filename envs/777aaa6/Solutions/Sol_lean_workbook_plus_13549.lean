-- Prove2me | solution 1 for lean_workbook_plus_13549
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:37.308711+00:00
-- url     : https://prove2.me/submissions/bf317ffa-8676-4b9f-9e4c-3e45174ea530

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (hxy : x ≥ y ∧ y ≥ z) (h : x * y + y * z + z * x = 1) : x * z < 1 / 2 := by
  have hp := mul_nonneg (sub_nonneg.mpr hxy.1) (sub_nonneg.mpr hxy.2)
  have hl : x*z ≤ 1/2 := by nlinarith [sq_nonneg y]
  by_contra hn
  have hy : y=0 := by nlinarith
  subst y
  have hx0 : 0 ≤ x := by linarith
  have hz0 : z ≤ 0 := by linarith
  have hp0 := mul_nonpos_of_nonneg_of_nonpos hx0 hz0
  nlinarith [h]
