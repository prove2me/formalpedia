-- Prove2me | solution 1 for lean_workbook_plus_70898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:23.468531+00:00
-- url     : https://prove2.me/submissions/6b23374e-85b7-4f77-b380-1d37ee7495ea

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℤ) :
    z^2 = (x^2 + 1) * (y^2 - 1) + 2006 ↔
    x^2 - y^2 + z^2 - x^2 * y^2 = 2005 := by
  constructor <;> intro h <;> nlinarith [h]

#print axioms solution
