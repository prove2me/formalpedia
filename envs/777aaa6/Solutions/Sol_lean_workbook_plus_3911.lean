-- Prove2me | solution 1 for lean_workbook_plus_3911
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:24.569394+00:00
-- url     : https://prove2.me/submissions/b02a388d-a3df-4b5b-8aa5-d31a6b55bd19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*(a^2 + b^2 + c^2) - (a^2*b + b^2*a + a^2*c + c^2*a + b^2*c + c^2*b) - 3*a*b*c := by
  (intros; linarith)
