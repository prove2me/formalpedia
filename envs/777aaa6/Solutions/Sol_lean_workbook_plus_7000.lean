-- Prove2me | solution 1 for lean_workbook_plus_7000
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:18.320589+00:00
-- url     : https://prove2.me/submissions/55b9bb1e-74a5-4a0d-90b6-cc0ca7120cb9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (a b c : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
  (h₂ : a * b * c = 1)
  (h₃ : a = x / y)
  (h₄ : b = y / z)
  (h₅ : c = z / x) :
  x / y * (y / z) * (z / x) = 1 := by
  (intros; simp_all)
