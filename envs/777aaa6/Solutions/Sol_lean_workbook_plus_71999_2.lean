-- Prove2me | solution 2 for lean_workbook_plus_71999
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:04.736771+00:00
-- url     : https://prove2.me/submissions/cca15b63-f886-4fd1-98c9-8380693a93e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (a * b + 1) * (b * c + 1) * (c * a + 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
