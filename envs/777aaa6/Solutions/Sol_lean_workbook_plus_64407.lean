-- Prove2me | solution 1 for lean_workbook_plus_64407
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:33.073493+00:00
-- url     : https://prove2.me/submissions/c7fe3bd0-c05d-4ba8-a670-5503b52e4bb7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 = (x^2 + y^2 - z^2)^2 + (2 * x * z)^2 + (2 * y * z)^2 := by
  (intros; linarith)
