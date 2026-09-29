-- Prove2me | solution 1 for lean_workbook_plus_63848
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:45.592772+00:00
-- url     : https://prove2.me/submissions/756bcfe3-3ec8-4bf0-bc91-d05f66b7354a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (h1 : a = x + y) (h2 : b = y + z) (h3 : c = z + x) (hx : x > 0 ∧ y > 0 ∧ z > 0) : a + b + c = 2 * (x + y + z) := by
  (intros; linarith)
