-- Prove2me | solution 1 for lean_workbook_plus_7364
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:08.611697+00:00
-- url     : https://prove2.me/submissions/13c5d476-d791-46d2-8ce0-44b93aeba6d7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℂ) : (x^3 - 6 * z^2 + 12 * z - 8 = 0 ∧ x = y ∧ y = z) ↔ x^3 - 6 * z^2 + 12 * z - 8 = 0 ∧ x = z ∧ y = z := by
  (intros; simp_all)
