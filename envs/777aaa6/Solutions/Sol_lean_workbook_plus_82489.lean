-- Prove2me | solution 1 for lean_workbook_plus_82489
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:23.856589+00:00
-- url     : https://prove2.me/submissions/dc50d9fe-957d-4fe6-848c-d425796e5b3a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
  (h₁ : x * y * z = 1)
  (h₂ : 1 / x^4 + 1 / y^4 + 1 / z^4 = 1 / 8) :
  16 / x^4 + 16 / y^4 + 16 / z^4 = 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
