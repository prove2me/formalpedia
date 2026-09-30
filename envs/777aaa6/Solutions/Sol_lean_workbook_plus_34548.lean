-- Prove2me | solution 1 for lean_workbook_plus_34548
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:19:32.975985+00:00
-- url     : https://prove2.me/submissions/01141f15-7cfe-4dda-8b47-5bff3a7848cd

import Mathlib

set_option autoImplicit false

theorem solution (k : Nat) (hk : 1 < k) :
    (1 : Real)/k^3 < 1/2*(1/(k-1)^2-1/k^2) := by
  have hkr : (1 : Real) < k := by exact_mod_cast hk
  have hkpos : (0 : Real) < k := by linarith
  have hkmpos : (0 : Real) < k-1 := by linarith
  have hid : (1 : Real)/2*(1/(k-1)^2-1/k^2)-1/k^3 =
      (3*(k:Real)-2)/(2*(k:Real)^3*((k:Real)-1)^2) := by
    field_simp [ne_of_gt hkpos, ne_of_gt hkmpos]
    ring
  have hnum : 0 < 3*(k:Real)-2 := by linarith
  have hrem : 0 < (3*(k:Real)-2)/(2*(k:Real)^3*((k:Real)-1)^2) := by
    positivity
  linarith

#print axioms solution
