-- Prove2me | solution 1 for lean_workbook_plus_22985
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:47:01.562005+00:00
-- url     : https://prove2.me/submissions/67c44718-ab71-41de-bc25-dba1d8fba5d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (1 : ℝ) / 1993 * (1 - 1 / (6 * 1993^2)) > 1 / 1994 := by
  norm_num
