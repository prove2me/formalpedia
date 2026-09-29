-- Prove2me | solution 1 for lean_workbook_plus_56431
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:06.242371+00:00
-- url     : https://prove2.me/submissions/be1d5dc0-e6a2-49aa-a38d-1b693aa31b1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≥ y ∧ y ≥ z)
  (h₂ : x * y + y * z + z * x = 1) :
  x * z ≤ 1 / 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
