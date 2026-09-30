-- Prove2me | solution 1 for lean_workbook_plus_7233
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:47:25.890265+00:00
-- url     : https://prove2.me/submissions/467cd43a-9286-4e7e-a960-6a133fbb8d32

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → x * (1 - x) * (x ^ 4 * (x ^ 2 + x + 1) + 1) < 1   := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hx2 : 0 < x^2 := pow_pos hx0 2
  have hx2lt : x^2 < 1 := by
    nlinarith only [mul_lt_mul_of_pos_left hx1 hx0, hx1]
  have hx4 : 0 < x^4 := pow_pos hx0 4
  have hx4lt : x^4 < 1 := by
    nlinarith only [mul_lt_mul_of_pos_left hx2lt hx2, hx2lt]
  have hsum : x^2+x+1 < 3 := by linarith only [hx2lt, hx1]
  have hprod : x^4*(x^2+x+1) < 3 :=
    lt_trans (mul_lt_mul_of_pos_left hsum hx4) (by nlinarith only [hx4lt])
  have hB : x^4*(x^2+x+1)+1 < 4 := by linarith only [hprod]
  have hA : 0 < x*(1-x) := mul_pos hx0 (by linarith only [hx1])
  have hquarter : x*(1-x)*4 ≤ 1 := by nlinarith only [sq_nonneg (2*x-1)]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hB hA) hquarter

#print axioms solution
