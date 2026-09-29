-- Prove2me | solution 1 for lean_workbook_plus_18441
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:47.156274+00:00
-- url     : https://prove2.me/submissions/a293f430-4d4f-4c2d-9689-a5ca827cd53c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c d : ℝ, (a^4 + b^4)*(c^4 + d^4) = (a^2*c^2 - b^2*d^2)^2 + (a^2*d^2 + b^2*c^2)^2 := by
  (intros; linarith)
