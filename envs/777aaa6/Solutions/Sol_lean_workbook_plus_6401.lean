-- Prove2me | solution 1 for lean_workbook_plus_6401
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:29.882142+00:00
-- url     : https://prove2.me/submissions/6b05029d-df00-4158-914e-ce321402edc0

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (a : ℝ) (hx : abs x ≥ 1) (h : x^5 - x^3 + x - 1 = a) :
x^6 - 1 ≥ 2 * a   := by
  have hid : x^6-1-2*a =
      (x-1)^2*((x^2-1/2)^2+3/4) := by
    rw [← h]
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (by norm_num))

#print axioms solution
