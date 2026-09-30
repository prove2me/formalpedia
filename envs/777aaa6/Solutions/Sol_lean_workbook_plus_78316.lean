-- Prove2me | solution 1 for lean_workbook_plus_78316
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T21:56:02.046338+00:00
-- url     : https://prove2.me/submissions/7290fe1f-1e11-4293-b27b-9a6b13a9958e

import Mathlib.Analysis.Complex.Basic

theorem solution : 7^7 < 2^20 := by
  norm_num
