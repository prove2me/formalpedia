-- Prove2me | solution 1 for lean_workbook_plus_63403
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:23.069081+00:00
-- url     : https://prove2.me/submissions/6f6bb671-586c-466b-85a1-ce3a3af1adca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a * b * (b - a) + b * c * (c - b) + c * a * (a - c) = (a - b) * (b - c) * (c - a) := by
  (intros; linarith)
