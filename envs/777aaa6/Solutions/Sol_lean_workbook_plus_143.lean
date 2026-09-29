-- Prove2me | solution 1 for lean_workbook_plus_143
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:50.456827+00:00
-- url     : https://prove2.me/submissions/37940521-0fbc-4843-ac0a-c238e953d489

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 1 + 1 = 2) : 1 / (1 + 1) = 1 / 2 := by
  norm_num
