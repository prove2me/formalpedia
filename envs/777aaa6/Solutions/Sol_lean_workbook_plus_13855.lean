-- Prove2me | solution 1 for lean_workbook_plus_13855
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:39.77625+00:00
-- url     : https://prove2.me/submissions/e2da8fa9-7d19-421d-bc10-50536748c275

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 0^2 = 0) : 1^2 * 0 + 0^2 * 1 + 0^2 * 1 = 0 := by
  norm_num
