-- Prove2me | solution 1 for lean_workbook_plus_64324
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:40:57.097482+00:00
-- url     : https://prove2.me/submissions/650944b3-6669-42a0-9e16-216a4ce64d40

import Mathlib.Analysis.Complex.Basic

theorem solution (a b d : ℤ) (h : d = a + b) : d * a + d * b ∣ (d * a)^2 + (d * b)^2 := by
  subst h
  exact Dvd.intro (a ^ 2 + b ^ 2) (by ring)
