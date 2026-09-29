-- Prove2me | solution 1 for lean_workbook_plus_34389
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:39.005757+00:00
-- url     : https://prove2.me/submissions/cd7e1233-d8d9-4fd5-a743-077cd29cd25e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 7 / 10 * (3 / 9 * (2 / 8)) = 42 / 720) : true := by
  norm_num
