-- Prove2me | solution 1 for lean_workbook_plus_43268
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:26:09.730116+00:00
-- url     : https://prove2.me/submissions/10988feb-fb9b-4f82-bb17-db32d94971c5

import Mathlib.Analysis.Complex.Basic

theorem solution : 1.61803399 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num
