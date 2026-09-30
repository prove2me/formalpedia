-- Prove2me | solution 1 for lean_workbook_plus_18297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:22.253506+00:00
-- url     : https://prove2.me/submissions/f3326654-b447-4c06-8422-f2ea0ef91cbd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (N : ℕ) (h : N > 10) : N ≥ 11 := by
  omega
