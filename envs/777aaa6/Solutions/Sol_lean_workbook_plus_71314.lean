-- Prove2me | solution 1 for lean_workbook_plus_71314
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:18.729347+00:00
-- url     : https://prove2.me/submissions/07db448a-ad12-4ee0-bc69-4fe051fb2a4c

import Mathlib
set_option autoImplicit false

theorem solution (x y a b : ℝ)
    (h0 : 0 < x ∧ 0 < y ∧ 0 < a ∧ 0 < b)
    (h1 : x = 8 * a) (h2 : y = 12 * b)
    (h3 : (x + y) / (a + b) = 9) : x = 2 * y := by
  have hne : a + b ≠ 0 := ne_of_gt (add_pos h0.2.2.1 h0.2.2.2)
  have h := (div_eq_iff hne).mp h3
  linarith

#print axioms solution
