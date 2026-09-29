-- Prove2me | solution 1 for lean_workbook_plus_38305
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:15.736917+00:00
-- url     : https://prove2.me/submissions/282b6286-1417-4e76-875d-8c42078cb8bc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (b^2 + d^2)^2 * (a^2 + c^2) + (a^2 + c^2)^2 * (b^2 + d^2) ≥ (b^2 + d^2) * (a^2 + c^2) * (a^2 + b^2 + c^2 + d^2) := by
  (intros; linarith)
