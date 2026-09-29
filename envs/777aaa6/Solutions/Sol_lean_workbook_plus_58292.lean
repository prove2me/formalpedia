-- Prove2me | solution 1 for lean_workbook_plus_58292
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:16.040224+00:00
-- url     : https://prove2.me/submissions/44a5c100-5db7-4416-b02f-95953993cc34

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ b c : ℝ, 2 * (b ^ 2 + c ^ 2) = (b + c) ^ 2 + (b - c) ^ 2 := by
  (intros; linarith)
