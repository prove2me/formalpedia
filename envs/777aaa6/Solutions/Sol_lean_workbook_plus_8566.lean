-- Prove2me | solution 1 for lean_workbook_plus_8566
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:51:14.829816+00:00
-- url     : https://prove2.me/submissions/401bfb30-1760-4e7d-b730-288f77995ec3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℤ)
  (h₀ : 4 * n + 3 = 1351) :
  n = 337 := by
  (intros; omega)
