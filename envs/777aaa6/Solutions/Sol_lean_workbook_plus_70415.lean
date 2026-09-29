-- Prove2me | solution 1 for lean_workbook_plus_70415
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:18.567012+00:00
-- url     : https://prove2.me/submissions/f3398702-55cf-4bc3-a15e-6c342488c38f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (a : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : a = x * y * z - 1 / (x * y * z))
  (h₂ : x - 1/y = a/6)
  (h₃ : y - 1/z = a/3)
  (h₄ : z - 1/x = a/2)
  (h₅ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x + y + z - 1/x - 1/y - 1/z = a := by
  (intros; linarith)
