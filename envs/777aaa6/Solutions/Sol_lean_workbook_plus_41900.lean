-- Prove2me | solution 1 for lean_workbook_plus_41900
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:53.970284+00:00
-- url     : https://prove2.me/submissions/2ac94449-e24a-447f-a78e-cc0461174393

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^4 + 4 * x^2 + 16 = (x^2 + 2 * x + 4) * (x^2 - 2 * x + 4) := by
  (intros; linarith)
