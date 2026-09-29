-- Prove2me | solution 1 for lean_workbook_plus_33576
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:11.590589+00:00
-- url     : https://prove2.me/submissions/a55ba536-6c4d-40b5-988a-f7223ae003ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (h₁ : a + b + c = 1) (h₂ : x = 1 / a) (h₃ : y = 1 / b) (h₄ : z = 1 / c) : (1 / x + 1 / y + 1 / z) ≤ 3 := by
  (intros; simp_all)
