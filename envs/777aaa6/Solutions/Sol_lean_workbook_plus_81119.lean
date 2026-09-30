-- Prove2me | solution 1 for lean_workbook_plus_81119
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:12:24.883623+00:00
-- url     : https://prove2.me/submissions/98b8a6bd-1c71-4413-b39e-ce45cfc70d10

import Mathlib

theorem solution (S E G I : ℝ) : S / (E + G + I) = 20 → E + G + I = S / 20 := by
  intro h
  have hd : E + G + I ≠ 0 := by
    intro hz
    simp [hz] at h
  have hm := (div_eq_iff hd).mp h
  linarith
