-- Prove2me | solution 1 for lean_workbook_plus_74296
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:04.342536+00:00
-- url     : https://prove2.me/submissions/261b6984-c235-4ca2-a6f2-2ae33befd261

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s : ℝ)
  (h₀ : r + s = 3)
  (h₁ : r * s = 1) :
  r^2 + s^2 = 7 := by
  (intros; nlinarith [sq_nonneg (r), sq_nonneg (s), sq_nonneg (r - s), sq_nonneg (r + s)])
