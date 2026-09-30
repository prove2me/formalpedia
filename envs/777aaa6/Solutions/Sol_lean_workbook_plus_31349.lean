-- Prove2me | solution 1 for lean_workbook_plus_31349
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:08.123395+00:00
-- url     : https://prove2.me/submissions/ad8d228b-56f3-4da2-b05a-bc067e103394

import Mathlib

set_option autoImplicit false

theorem solution (p : Nat) (h0 : p > 0) (h1 : p % 2 = 1) :
    ((p-1)/2)^2+(p-1)/2+1 = (p^2+3)/4 := by
  have hp : p = 2*(p/2)+1 := by omega
  have hh : (p-1)/2 = p/2 := by omega
  have hid : p^2+3 = 4*((p/2)^2+p/2+1) := by
    conv_lhs => rw [hp]
    ring
  rw [hh, hid]
  omega

#print axioms solution
