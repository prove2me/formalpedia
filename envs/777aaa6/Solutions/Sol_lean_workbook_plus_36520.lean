-- Prove2me | solution 1 for lean_workbook_plus_36520
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:35.435802+00:00
-- url     : https://prove2.me/submissions/a7ba5a8b-62e0-4160-80de-99db47078035

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  9 * (a^2 + b^2 + c^2) = (2 * a + 2 * b - c)^2 + (2 * b + 2 * c - a)^2 + (2 * c + 2 * a - b)^2 := by
  (intros; linarith)
