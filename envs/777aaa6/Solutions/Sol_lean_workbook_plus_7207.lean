-- Prove2me | solution 1 for lean_workbook_plus_7207
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:27.274836+00:00
-- url     : https://prove2.me/submissions/6ec3dcf7-4bc5-499e-925f-f8883205ce4d

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : (4 * x ^ 2 * y ^ 2) / (x ^ 2 + y ^ 2) ^ 2 + x ^ 2 / y ^ 2 + y ^ 2 / x ^ 2 >= 3   := by
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
  have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
  have hs : 0 < x^2+y^2 := add_pos hx2 hy2
  have hd : 0 < x^2*y^2*(x^2+y^2)^2 :=
    mul_pos (mul_pos hx2 hy2) (pow_pos hs 2)
  have hx4 : 0 ≤ x^4 := by nlinarith only [sq_nonneg (x^2)]
  have hy4 : 0 ≤ y^4 := by nlinarith only [sq_nonneg (y^2)]
  have hn : 0 ≤ (x^2-y^2)^2*(x^4+x^2*y^2+y^4) :=
    mul_nonneg (sq_nonneg _) (add_nonneg
      (add_nonneg hx4 (mul_nonneg hx2.le hy2.le)) hy4)
  have hid : 4*x^2*y^2/(x^2+y^2)^2 + x^2/y^2 + y^2/x^2 - 3 =
      (x^2-y^2)^2*(x^4+x^2*y^2+y^4)/(x^2*y^2*(x^2+y^2)^2) := by
    field_simp [hx, hy, ne_of_gt hs]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg hn hd.le

#print axioms solution
