-- Prove2me | solution 1 for lean_workbook_plus_32072
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:08.516286+00:00
-- url     : https://prove2.me/submissions/e32e5135-bffb-4389-9118-eebd58e83f8c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 14 * 13 = 182) : 182 / 2 = 91 := by
  norm_num
