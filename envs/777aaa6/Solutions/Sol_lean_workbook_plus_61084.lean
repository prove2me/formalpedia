-- Prove2me | solution 1 for lean_workbook_plus_61084
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:23.219535+00:00
-- url     : https://prove2.me/submissions/11b0cf66-62ff-4500-9f84-b7b4205573b9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≤ y ∧ y ≤ z) :
  (x + y + z) * (x*y + y*z + z*x) ≥ 9*x*y*z + (y - x)*(z - x)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
