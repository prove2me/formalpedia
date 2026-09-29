-- Prove2me | solution 1 for lean_workbook_plus_22690
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:30.812403+00:00
-- url     : https://prove2.me/submissions/5cf16637-a4b1-4fdd-b6df-716d631d315d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a^2 + b^2 + c^2)^2 - 3 * (a^3 * b + b^3 * c + c^3 * a) =
    1 / 2 * ((a^2 - b^2 + 2 * b * c - a * b - a * c)^2 +
      (b^2 - c^2 + 2 * c * a - b * c - b * a)^2 +
      (c^2 - a^2 + 2 * a * b - c * a - c * b)^2) := by
  (intros; linarith)
