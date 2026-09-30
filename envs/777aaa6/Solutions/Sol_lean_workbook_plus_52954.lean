-- Prove2me | solution 1 for lean_workbook_plus_52954
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:38:54.18898+00:00
-- url     : https://prove2.me/submissions/a75a99bd-8027-4ca7-9bef-a218f1cd5963

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.Nat

theorem solution (x y : ℤ) : (gcd x y)^2 ∣ x^2 + y^2 := by
  exact dvd_add (pow_dvd_pow_of_dvd (gcd_dvd_left x y) 2)
    (pow_dvd_pow_of_dvd (gcd_dvd_right x y) 2)

#print axioms solution
