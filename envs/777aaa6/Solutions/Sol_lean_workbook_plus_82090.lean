-- Prove2me | solution 1 for lean_workbook_plus_82090
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:06.546589+00:00
-- url     : https://prove2.me/submissions/62bf53d6-4f2d-4f71-a7ac-1db24630bb94

import Mathlib

theorem solution (n : ℕ) : (n + 1) ^ 2 - n ^ 2 = 2 * n + 1 := by
  have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  omega
