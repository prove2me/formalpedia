-- Prove2me | solution 1 for lean_workbook_plus_73481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:36:11.428812+00:00
-- url     : https://prove2.me/submissions/5b6fdc49-899b-4db2-897f-d599d55644e7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.GCDMonoid.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b : ℤ) (h : a + 1 = b) : gcd a b = 1 := by
  rw [← h]
  calc
    gcd a (a + 1) = gcd a 1 := gcd_eq_of_dvd_sub_right (by convert dvd_refl a using 1 <;> ring)
    _ = 1 := gcd_one_right a
