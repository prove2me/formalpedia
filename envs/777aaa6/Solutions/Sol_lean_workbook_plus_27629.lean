-- Prove2me | solution 1 for lean_workbook_plus_27629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:20.583664+00:00
-- url     : https://prove2.me/submissions/957c3a00-e4d1-4f54-aeb7-52b9371c845d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) :
  Real.sqrt ((a^2 + b^2 + 2 * a + 1) / (a^2 + b^2 + 1)) +
    Real.sqrt ((a^2 + b^2 - 2 * a + 1) / (a^2 + b^2 + 1)) =
    Real.sqrt (1 + (2 * a) / (a^2 + b^2 + 1)) +
    Real.sqrt (1 - (2 * a) / (a^2 + b^2 + 1)) := by
  (intros; field_simp; ring)
