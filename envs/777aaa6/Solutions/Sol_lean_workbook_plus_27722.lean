-- Prove2me | solution 1 for lean_workbook_plus_27722
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:07.720654+00:00
-- url     : https://prove2.me/submissions/2bf70879-28c8-4ee4-bd13-58779937c12c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x * y * z = 1)
  (h₁ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x^2 + y^2 + z^2 ≥ x * y + y * z + z * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
