-- Prove2me | solution 1 for lean_workbook_plus_4164
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:25.380266+00:00
-- url     : https://prove2.me/submissions/fab04aa6-0e1f-4266-b3f7-6b5ff6d1dea5

import Mathlib

theorem solution {a b c : ℝ} :
    a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a) ≥
      3 * (a - b) * (b - c) := by
  nlinarith [sq_nonneg (a - 2 * b + c)]
