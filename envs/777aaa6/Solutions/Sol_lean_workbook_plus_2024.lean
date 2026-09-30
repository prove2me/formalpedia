-- Prove2me | solution 1 for lean_workbook_plus_2024
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:34.445984+00:00
-- url     : https://prove2.me/submissions/ca8e26ce-4508-423f-af1d-021c06840fba

import Mathlib

theorem solution (a : ℝ) : a ^ 2 + 1 / 9 ≥ 2 / 3 * a := by
  nlinarith [sq_nonneg (a - 1 / 3)]
