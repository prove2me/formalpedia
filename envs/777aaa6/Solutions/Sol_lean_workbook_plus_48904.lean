-- Prove2me | solution 1 for lean_workbook_plus_48904
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:55.059441+00:00
-- url     : https://prove2.me/submissions/8868ad77-d6ef-4fce-862f-3ae23421c7cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 111 * 10 + 11 + 1 = 1122) : 111 * 10 + 11 + 1 = 1122 := by
  norm_num
