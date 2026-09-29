-- Prove2me | solution 1 for lean_workbook_plus_78582
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:52.894838+00:00
-- url     : https://prove2.me/submissions/040d0e16-9826-4042-8dae-f3755d9e6a9a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 10) (h₂ : x*y + y*z + z*x = 54) (h₃ : x*y*z = 70) : (x = 9 ∧ y = 8 ∧ z = 7) ∨ (x = -9 ∧ y = -8 ∧ z = -7) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
