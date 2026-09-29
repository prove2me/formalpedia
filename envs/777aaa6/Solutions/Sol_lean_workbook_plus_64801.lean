-- Prove2me | solution 1 for lean_workbook_plus_64801
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:22.299712+00:00
-- url     : https://prove2.me/submissions/1d914319-747d-4c64-a5d6-aeca6e2eafe4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s : ℂ) (hr : r^2 - 8 * r + 12 = 0) (hs : s^2 - 8 * s + 12 = 0) : r + s + (4 - r) + (4 - s) = 8 := by
  (intros; ring)
