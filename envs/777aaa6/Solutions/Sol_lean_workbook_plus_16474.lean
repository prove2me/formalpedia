-- Prove2me | solution 1 for lean_workbook_plus_16474
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:44:32.34526+00:00
-- url     : https://prove2.me/submissions/2e81d982-5076-401e-bd84-37d1d2f74c8a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a k : ℤ) : (3 * k ^ 2 + 11 * k + a - 9 = 3 * k ^ 2 + k + 3 - 2 * a) ↔ 3 * a + 10 * k = 12 := by
  (intros; omega)
