-- Prove2me | solution 1 for lean_workbook_plus_15629
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:03.015032+00:00
-- url     : https://prove2.me/submissions/2cccfb9b-4fef-4d93-850e-aae39c297e35

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z a : ℝ)
  (h₀ : x*y*z = a^3)
  (h₁ : 4 ≥ a^3 + 3*a^2) :
  a ≤ 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (a), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - a), sq_nonneg (y - z), sq_nonneg (y - a), sq_nonneg (z - a), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + a), sq_nonneg (y + z), sq_nonneg (y + a), sq_nonneg (z + a)])
