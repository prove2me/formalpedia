-- Prove2me | solution 1 for lean_workbook_plus_66080
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:42.148947+00:00
-- url     : https://prove2.me/submissions/c72fdcd8-023b-4513-88a4-6220aca8bd7e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c d : ℝ} (habc : a + b = c + d) (hab : a - c = d - b) : a^2 - 2 * a * c + c^2 = d^2 - 2 * b * d + b^2 := by
  calc
    a^2-2*a*c+c^2 = (a-c)^2 := by ring
    _ = (d-b)^2 := by rw [hab]
    _ = d^2-2*b*d+b^2 := by ring
