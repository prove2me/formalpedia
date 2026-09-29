-- Prove2me | solution 1 for lean_workbook_plus_193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:16.26008+00:00
-- url     : https://prove2.me/submissions/062ed041-0f25-49a0-b4e3-3d1ad25f1a7f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℤ, (a^3 + b^3 + c^3) - (a + b + c) = a*(a - 1)*(a + 1) + b*(b - 1)*(b + 1) + c*(c - 1)*(c + 1) := by
  (intros; linarith)
