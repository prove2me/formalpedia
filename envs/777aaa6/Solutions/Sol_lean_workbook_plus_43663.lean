-- Prove2me | solution 1 for lean_workbook_plus_43663
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:05.567171+00:00
-- url     : https://prove2.me/submissions/f6219a85-ddf9-4f40-a94e-8c35ef192a2a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y : ℝ, x^5 + y^5 = (x + y) * (x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4) := by
  (intros; linarith)
