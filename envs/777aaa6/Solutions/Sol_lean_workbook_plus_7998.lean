-- Prove2me | solution 1 for lean_workbook_plus_7998
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:33:48.208043+00:00
-- url     : https://prove2.me/submissions/0d6536b6-7efa-4941-beff-aa0ee821549c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 15 * 87 = 1305) : 15 * 87 = 1305 := by
  norm_num
