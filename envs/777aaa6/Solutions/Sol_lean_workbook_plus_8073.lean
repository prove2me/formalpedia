-- Prove2me | solution 1 for lean_workbook_plus_8073
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:42.918864+00:00
-- url     : https://prove2.me/submissions/0666d4be-7876-4f84-8a0f-96ec9b42c29e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x < 0 ∧ y < 0 ∧ z < 0)
  (h₁ : x^4 + y^4 + z^4 = 3) :
  x^3 + y^3 + z^3 + (x^2 * y + y^2 * z + z^2 * x) ≤ 6 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
