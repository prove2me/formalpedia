-- Prove2me | solution 1 for lean_workbook_plus_36276
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:49.320453+00:00
-- url     : https://prove2.me/submissions/8fc71a43-4b7b-4c6b-9e8e-cfe1631e62b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (h : a + b + c = 0) : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - a * b - b * c - c * a) := by
  (intros; linarith)
