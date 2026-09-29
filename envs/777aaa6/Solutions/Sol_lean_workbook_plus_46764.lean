-- Prove2me | solution 1 for lean_workbook_plus_46764
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:14:35.742332+00:00
-- url     : https://prove2.me/submissions/6fda53e2-99ff-4918-b7b0-2f7f93f0019f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y = x / 2) (h₂ : y > 0) : x ≥ y := by
  (intros; linarith)
