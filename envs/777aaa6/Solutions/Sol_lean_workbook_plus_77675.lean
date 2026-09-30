-- Prove2me | solution 1 for lean_workbook_plus_77675
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:47:03.287834+00:00
-- url     : https://prove2.me/submissions/8c1e9851-e3f6-43dd-9015-a0f604a9ebfd

import Mathlib

theorem solution (x y : ℝ) :
    25 * (x ^ 2 + y ^ 2) = (x ^ 2 + y ^ 2) ^ 2 ↔
      (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2 - 25) = 0 := by
  constructor <;> intro h <;> nlinarith
