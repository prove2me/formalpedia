-- Prove2me | solution 1 for lean_workbook_plus_70802
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:06.210581+00:00
-- url     : https://prove2.me/submissions/1e36fa81-572c-4dd5-92e7-921347513a3f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a - b) ^ 3 = a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3 := by
  (intros; linarith)
