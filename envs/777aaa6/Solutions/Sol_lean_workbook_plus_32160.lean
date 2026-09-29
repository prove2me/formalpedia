-- Prove2me | solution 1 for lean_workbook_plus_32160
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:53:50.689852+00:00
-- url     : https://prove2.me/submissions/d7fff3b1-44bc-4338-a8d3-bbe670760aef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : b*c ≤ b^2 - b*c + c^2 := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
