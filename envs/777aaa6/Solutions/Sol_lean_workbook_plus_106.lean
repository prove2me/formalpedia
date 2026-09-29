-- Prove2me | solution 1 for lean_workbook_plus_106
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:21.056968+00:00
-- url     : https://prove2.me/submissions/310ac247-4b3f-420e-960c-7cb2fb4f1e77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ a b c : ℝ, (a + b + c) ^ 2 = (a + 2 * b) * (a + 2 * c) + (b - c) ^ 2 := by
  (intros; linarith)
