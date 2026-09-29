-- Prove2me | solution 1 for lean_workbook_plus_50935
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:40.470036+00:00
-- url     : https://prove2.me/submissions/483f6725-6416-4775-9631-19da0ebc0d73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ b c : ℝ, (b^2 + c^2)^3 = b^6 + c^6 + 3 * b^2 * c^2 * (b^2 + c^2) := by
  (intros; linarith)
