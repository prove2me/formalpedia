-- Prove2me | solution 1 for lean_workbook_plus_72451
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:52.701304+00:00
-- url     : https://prove2.me/submissions/441fcbae-fccd-4e50-8294-f332e5efdd0c

import Mathlib

theorem solution (a : ℝ) (h₀ : a ≠ 2) :
    1 / (2 - a) = a * (a - 1)^2 / (2 * (2 - a)) + 1 / 2 * (a^2 + 1) := by
  have hd : 2 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h₀)
  field_simp
  ring

#print axioms solution
