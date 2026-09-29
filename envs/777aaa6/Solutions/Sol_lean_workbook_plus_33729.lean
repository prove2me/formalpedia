-- Prove2me | solution 1 for lean_workbook_plus_33729
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:30.458949+00:00
-- url     : https://prove2.me/submissions/e8b74178-7a4e-48fe-a4be-f2c11d042f4a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ s : ℝ, s^2 - 6 * s + 9 ≥ (s - 3)^2 := by
  (intros; linarith)
