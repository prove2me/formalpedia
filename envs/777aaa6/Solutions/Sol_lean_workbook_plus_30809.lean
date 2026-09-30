-- Prove2me | solution 1 for lean_workbook_plus_30809
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:28:06.510837+00:00
-- url     : https://prove2.me/submissions/7e29abd5-e2af-457b-a53f-36d199120b55

import Mathlib

set_option autoImplicit false

theorem solution (x y : Real) (m n : Nat)
    (hx : x^m ≥ y^m) (hn : x^n ≥ y^n) :
    2*(x^(m+n)+y^(m+n)) ≥ (x^m+y^m)*(x^n+y^n) := by
  have hp := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hn)
  simp only [pow_add]
  nlinarith

#print axioms solution
