-- Prove2me | solution 1 for lean_workbook_plus_25454
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:52.22102+00:00
-- url     : https://prove2.me/submissions/b909cc89-fdd7-45b3-bc82-4ac0b8cd050e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * a ^ 2 + b * c = a * (a + b + c) + (a - b) * (a - c) := by
  (intros; linarith)
