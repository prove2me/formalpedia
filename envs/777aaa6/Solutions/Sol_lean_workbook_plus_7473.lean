-- Prove2me | solution 1 for lean_workbook_plus_7473
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:33:58.680222+00:00
-- url     : https://prove2.me/submissions/01eb0fbc-ac27-4546-935e-0a6fc0cbfd18

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 900 = 2 * 2 * 9 * 5 * 5) : true := by
  norm_num
