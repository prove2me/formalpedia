-- Prove2me | solution 1 for lean_workbook_plus_61403
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:55.609211+00:00
-- url     : https://prove2.me/submissions/559d421d-b16b-4c12-ae6a-53cc15ecbcec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^4 - 4 * x + 3 = (1 - x)^2 * (x^2 + 2 * x + 3) := by
  (intros; linarith)
