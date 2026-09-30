-- Prove2me | solution 1 for lean_workbook_plus_32615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:45.778679+00:00
-- url     : https://prove2.me/submissions/b0fb6693-1aa8-4f32-a22a-4ccf08f711f1

import Mathlib

set_option autoImplicit false

theorem solution (x y z a b c : Rat)
    (h0 : 0 < a ∧ 0 < b ∧ 0 < c) (h1 : x+y+z = a)
    (h2 : 1/x+1/y+1/z = b) (h3 : x*y*z = c)
    (h4 : 0 < x ∧ 0 < y ∧ 0 < z) : x*y+y*z+z*x = b*c := by
  rw [← h2, ← h3]
  field_simp [ne_of_gt h4.1, ne_of_gt h4.2.1, ne_of_gt h4.2.2]
  ring

#print axioms solution
