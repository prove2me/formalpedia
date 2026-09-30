-- Prove2me | solution 1 for lean_workbook_plus_68004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:44.150946+00:00
-- url     : https://prove2.me/submissions/afba8f7b-8279-479b-8b07-f64be2addc59

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + (a^2 + b^2 + c^2)^3 / 4 ≥
      (a^2 + b^2 + c^2) * (a + b + c)^4 / 12 +
        (a + b - 2 * c)^2 * (b + c - 2 * a)^2 * (c + a - 2 * b)^2 / 27 +
        (a + b + c)^6 / 54 := by
  apply le_of_eq
  ring

#print axioms solution
