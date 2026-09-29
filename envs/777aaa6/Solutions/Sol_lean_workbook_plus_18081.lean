-- Prove2me | solution 1 for lean_workbook_plus_18081
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:33.759642+00:00
-- url     : https://prove2.me/submissions/dacf2d85-7cce-4a18-8fe0-834a6a1ec0ee

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a + a * b * c ≥ 4 := by
  have hab1 : 1 ≤ a*b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hbc1 : 1 ≤ b*c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hca1 : 1 ≤ c*a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have habc1 : 1 ≤ a*b*c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega
