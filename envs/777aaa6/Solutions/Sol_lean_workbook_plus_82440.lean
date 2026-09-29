-- Prove2me | solution 1 for lean_workbook_plus_82440
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:32.588358+00:00
-- url     : https://prove2.me/submissions/3a45b06b-e05a-4b01-aed4-b127eb1deff6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^5 - 15 * x^4 + 85 * x^3 - 225 * x^2 + 274 * x - 120 = (x-1)*(x-2)*(x-3)*(x-4)*(x-5) := by
  (intros; linarith)
