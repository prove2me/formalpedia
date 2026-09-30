-- Prove2me | solution 1 for lean_workbook_plus_7004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:04.416327+00:00
-- url     : https://prove2.me/submissions/2da15fe6-00bd-407a-bda6-c9c22a6ae3ff

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 → Real.sqrt (3 - 2 * x) ≤ 1 ∧ Real.sqrt (3 - 2 * y) ≤ 1 ∧ Real.sqrt (3 - 2 * z) ≤ 1 → x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 ∧ x ^ 2 + y ^ 2 + z ^ 2 ≤ x ^ 3 + y ^ 3 + z ^ 3   := by
  intro x y z hxyz _hsqrt
  constructor
  · nlinarith only [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
  · have hx : 0 ≤ x^2*(x-1) := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hxyz.1)
    have hy : 0 ≤ y^2*(y-1) := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hxyz.2.1)
    have hz : 0 ≤ z^2*(z-1) := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hxyz.2.2)
    nlinarith only [hx, hy, hz]

#print axioms solution
