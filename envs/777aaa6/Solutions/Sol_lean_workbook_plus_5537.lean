-- Prove2me | solution 1 for lean_workbook_plus_5537
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:36.736093+00:00
-- url     : https://prove2.me/submissions/50630ec2-dd91-48b0-9481-6c43c9f08af3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : y ≠ 0) (h₂ : 7 - (x - y) ^ 2 = 2 * (x - y) - 8) : (x - y) ^ 2 + 2 * (x - y) - 15 = 0 := by
  (intros; linarith)
