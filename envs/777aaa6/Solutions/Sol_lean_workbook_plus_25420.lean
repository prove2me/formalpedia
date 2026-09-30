-- Prove2me | solution 1 for lean_workbook_plus_25420
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:47.50834+00:00
-- url     : https://prove2.me/submissions/9edcaea2-c5a7-4333-9481-ae91d5339b7b

import Mathlib
set_option autoImplicit false

theorem solution (w : ℂ) (hw : w ^ 3 = 1) (hw' : w ≠ 1) : w ^ 5 + w + 1 = 0   := by
  have hprod : (w - 1) * (w ^ 2 + w + 1) = 0 := by
    calc
      (w - 1) * (w ^ 2 + w + 1) = w ^ 3 - 1 := by ring
      _ = 0 := by rw [hw, sub_self]
  have hquad : w ^ 2 + w + 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hw')
  calc
    w ^ 5 + w + 1 = w ^ 2 * w ^ 3 + w + 1 := by ring
    _ = w ^ 2 + w + 1 := by rw [hw, mul_one]
    _ = 0 := hquad

#print axioms solution
