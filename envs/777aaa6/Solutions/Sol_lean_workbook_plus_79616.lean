-- Prove2me | solution 1 for lean_workbook_plus_79616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:35:53.846458+00:00
-- url     : https://prove2.me/submissions/6469473b-7ec2-4c64-8f3a-7dd0f2908477

import Mathlib

theorem solution {u v a b : ℝ}
    (ha : a + b = 2 * u) (hb : a * b = v ^ 2) :
    v ^ 4 * (4 * u ^ 2 - 2 * v ^ 2 - 2) ≥ 2 * u * (v ^ 2 - 1) ↔
      2 * v ^ 4 * u ^ 2 + (1 - v ^ 2) * u - v ^ 6 - v ^ 4 ≥ 0 := by
  constructor <;> intro h <;> nlinarith
