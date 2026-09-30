-- Prove2me | solution 1 for lean_workbook_plus_51478
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:34:08.285932+00:00
-- url     : https://prove2.me/submissions/de199c06-f1ea-490e-a9b1-357c7cb77d97

import Mathlib
set_option autoImplicit false

theorem solution (k l m : ℕ) : 2 ^ (k + l) + 2 ^ (l + m) + 2 ^ (m + k) ≤ 2 ^ (k + l + m + 1) + 1   := by
  have helper (x y z : ℝ) (hx : 1 <= x) (hy : 1 <= y) (hz : 1 <= z) :
      x * y + y * z + z * x <= 2 * x * y * z + 1 := by
    have hxy : 1 <= x * y := one_le_mul_of_one_le_of_one_le hx hy
    have h1 : 0 <= z * (x - 1) * (y - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hx)) (sub_nonneg.mpr hy)
    have h2 : 0 <= (z - 1) * (x * y - 1) :=
      mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hxy)
    nlinarith only [h1, h2]
  have h := helper ((2 : ℝ)^k) (2^l) (2^m)
    (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hreal : (2 : ℝ)^(k + l) + 2^(l + m) + 2^(m + k) <=
      2^(k + l + m + 1) + 1 := by
    simp only [pow_add, pow_one]
    nlinarith only [h]
  exact_mod_cast hreal

#print axioms solution
