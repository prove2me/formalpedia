-- Prove2me | solution 1 for lean_workbook_plus_55606
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:15.475584+00:00
-- url     : https://prove2.me/submissions/afe05ad2-9ebe-492b-be17-37c40f2a96c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  (x^2 - 3 * x - 2)^2 - 3 * (x^2 - 3 * x - 2) - 2 - x =
    (x^2 - 4 * x - 2) * (x^2 - 2 * x - 4) := by
  (intros; linarith)
