-- Prove2me | solution 1 for lean_workbook_plus_79991
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:08.364035+00:00
-- url     : https://prove2.me/submissions/81db73c0-2ffe-427d-b21e-f86a06f31edb

import Mathlib

theorem solution (a : ℝ) (ha : a^2 - 3*a + 1 = 0) :
    a^3/(a^6 + 1) = 1/18 := by
  have hpoly : a^6 - 18*a^3 + 1 = 0 := by
    calc
      a^6 - 18*a^3 + 1 =
          (a^2 - 3*a + 1) * (a^4 + 3*a^3 + 8*a^2 + 3*a + 1) := by ring
      _ = 0 := by rw [ha]; ring
  have hden : 0 < a^6 + 1 := by positivity
  apply (div_eq_iff (ne_of_gt hden)).2
  nlinarith only [hpoly]
