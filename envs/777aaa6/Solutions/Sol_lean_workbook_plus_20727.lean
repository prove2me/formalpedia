-- Prove2me | solution 1 for lean_workbook_plus_20727
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:12.752026+00:00
-- url     : https://prove2.me/submissions/180f032c-87ff-4cdd-b0e4-b1cd8e6573bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, x^8 + x^5 + x^4 + x^3 + x + 1 = (x + 1) * (x^2 - x + 1) * (x^2 + x + 1) * (x^3 - x^2 + 1) := by
  (intros; linarith)
