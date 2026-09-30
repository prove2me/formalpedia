-- Prove2me | solution 1 for lean_workbook_plus_29554
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:00.798934+00:00
-- url     : https://prove2.me/submissions/374450aa-d7f2-48fc-b525-a598d6d61f94

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a / (a + 2 * b + 1) + b / (b + 2 * a + 1) = 1 / 2) : a + b ≤ 2   := by
  have hda : 0 < a + 2 * b + 1 := by positivity
  have hdb : 0 < b + 2 * a + 1 := by positivity
  field_simp [ne_of_gt hda, ne_of_gt hdb] at hab
  have hc : (a + b - 2) * (3 * (a + b) + 2) ≤ 0 := by
    nlinarith only [hab, sq_nonneg (a - b)]
  by_contra! hs
  have hp : 0 < (a + b - 2) * (3 * (a + b) + 2) :=
    mul_pos (by linarith only [hs]) (by positivity)
  exact (not_lt_of_ge hc) hp

#print axioms solution
