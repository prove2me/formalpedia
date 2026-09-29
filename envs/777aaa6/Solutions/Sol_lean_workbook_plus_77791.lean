-- Prove2me | solution 1 for lean_workbook_plus_77791
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:36.218794+00:00
-- url     : https://prove2.me/submissions/84a1a66d-1b56-4200-9e8f-90b0794084ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℂ) : x^6 + 1 = (x^2 + 1) * (x^4 - x^2 + 1) := by
  (intros; ring)
