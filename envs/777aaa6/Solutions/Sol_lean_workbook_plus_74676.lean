-- Prove2me | solution 1 for lean_workbook_plus_74676
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:25:07.681289+00:00
-- url     : https://prove2.me/submissions/cb7cb415-6ee7-452e-99bb-66d6eaf622d6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y) * (x + z) * (y + z) ≥
      (8 / 9) * (x + y + z) * (x * y + x * z + y * z) := by
  have hn : 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 := by positivity
  nlinarith

#print axioms solution
