-- Prove2me | solution 1 for lean_workbook_plus_45531
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:01.306229+00:00
-- url     : https://prove2.me/submissions/b67bcd34-5a36-44a9-b9c5-55433cee1182

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) : x ^ 2 + y ^ 2 ≤ 1 + x * y   := by
  nlinarith only [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2),
    mul_nonneg hx.1 (sub_nonneg.mpr hx.2),
    mul_nonneg hy.1 (sub_nonneg.mpr hy.2)]

#print axioms solution
