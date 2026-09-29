-- Prove2me | solution 1 for lean_workbook_plus_72942
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:36.243129+00:00
-- url     : https://prove2.me/submissions/bafe3c98-4e72-4f3d-a1e6-edd64b71fe3c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 3) (h₂ : x*y + y*z + z*x = 9) (h₃ : x*y*z = 10) : x = 2 ∧ y = 1 ∧ z = 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
