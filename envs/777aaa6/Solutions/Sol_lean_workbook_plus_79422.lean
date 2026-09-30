-- Prove2me | solution 1 for lean_workbook_plus_79422
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:57.960052+00:00
-- url     : https://prove2.me/submissions/3f26583a-87d7-4398-b94a-6056b781cf23

import Mathlib

theorem solution (a b c : ℝ)
    (h0 : 0 < a ∧ 0 < b ∧ 0 < c)
    (h1 : a + b + c = 1) (h2 : 23 * a + 23 * b = 12 * c) :
    c / (a + b) = 23 / 12 := by
  apply (div_eq_iff (ne_of_gt (add_pos h0.1 h0.2.1))).2
  linarith
