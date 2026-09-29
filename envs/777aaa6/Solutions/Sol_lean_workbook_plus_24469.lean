-- Prove2me | solution 1 for lean_workbook_plus_24469
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:18.938085+00:00
-- url     : https://prove2.me/submissions/082da978-6d6e-4913-950f-bdf4eeb8f995

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (a^2 - Real.sqrt 2 * b)^2 + (b^2 - 1)^2 ≥ 0 := by
  (intros; positivity)
