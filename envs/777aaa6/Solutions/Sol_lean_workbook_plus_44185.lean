-- Prove2me | solution 1 for lean_workbook_plus_44185
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:40.740985+00:00
-- url     : https://prove2.me/submissions/b9969f58-0a0c-4651-9cb2-e77633b35fec

import Mathlib
set_option autoImplicit false

theorem solution  (t0 t1 t2 : ℝ)
  (h0 : t0 = 1 + t0 / 2 + t1 / 2)
  (h1 : t1 = 1 + t0 / 2 + t2 / 2)
  (h2 : t2 = 1 + t0 / 2) :
  t2 = 8 ∧ t1 = 12 ∧ t0 = 14   := by
  apply And.intro
  linarith only [h0, h1, h2]
  apply And.intro
  linarith only [h0, h1, h2]
  linarith only [h0, h1, h2]

#print axioms solution
