-- Prove2me | solution 1 for lean_workbook_plus_57420
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:37:26.856838+00:00
-- url     : https://prove2.me/submissions/f6dd58c3-0a7a-4eb7-b259-e815d8dd5472

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℤ) : a + 2 * 1 - 5 * (-1) = 13 ↔ a = 6 := by
  (intros; omega)
