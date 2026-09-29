-- Prove2me | solution 1 for lean_workbook_plus_32266
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:04.545284+00:00
-- url     : https://prove2.me/submissions/b52e0a55-f201-425c-8233-b66f8ef66a7c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, -4 * x ^ 2 + 6 * x - 1 - (x + 1) + 2 * x = -(4 * x ^ 2 - 7 * x + 2) := by
  (intros; linarith)
