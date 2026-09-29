-- Prove2me | solution 1 for lean_workbook_plus_62193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:04.596159+00:00
-- url     : https://prove2.me/submissions/cb863358-3185-42e4-9d1b-4b44db7e8d22

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) : a^4 - 16 * a^3 + 94 * a^2 - 240 * a + 225 = (a - 3)^2 * (a - 5)^2 := by
  (intros; linarith)
