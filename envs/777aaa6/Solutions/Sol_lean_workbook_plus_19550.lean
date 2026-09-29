-- Prove2me | solution 1 for lean_workbook_plus_19550
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:31.342084+00:00
-- url     : https://prove2.me/submissions/256da6f7-5805-4ee2-8abb-2c0007102ceb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v : ℝ) : (u^3 - Real.sqrt 3 * u^2 * v - (3 - Real.sqrt 3) * u * v^2 + v^3)^2 ≥ 0 := by
  (intros; positivity)
