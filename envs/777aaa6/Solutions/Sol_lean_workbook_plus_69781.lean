-- Prove2me | solution 1 for lean_workbook_plus_69781
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:20.046987+00:00
-- url     : https://prove2.me/submissions/4a0ca708-279f-41ed-bee5-cbbf98ba3ec4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s : ℝ) (hs : 0 ≤ s) : 0 < s^15 + 57 * s^14 + 507 * s^13 + 1820 * s^12 + 4368 * s^11 + 8008 * s^10 + 11440 * s^9 + 12870 * s^8 + 11440 * s^7 + 8008 * s^6 + 4368 * s^5 + 1820 * s^4 + 560 * s^3 + 120 * s^2 + 16 * s + 1 := by
  (intros; positivity)
