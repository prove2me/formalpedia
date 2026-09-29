-- Prove2me | solution 1 for lean_workbook_plus_45673
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:12.815985+00:00
-- url     : https://prove2.me/submissions/81247b10-4b97-44b3-9125-8de73321776d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : 3 * x * y = 30) : x * y = 10 := by
  (intros; linarith)
