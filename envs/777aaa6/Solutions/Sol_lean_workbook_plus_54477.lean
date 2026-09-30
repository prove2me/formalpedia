-- Prove2me | solution 1 for lean_workbook_plus_54477
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:13:09.219067+00:00
-- url     : https://prove2.me/submissions/efdf6539-2883-4b55-968d-fdef258a4c7d

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℕ → ℝ)
  (h₀ : ∀ n, x (n + 2) - x (n + 1) = -(y (n + 1) + y n))
  (h₁ : ∀ n, y (n + 2) - y (n + 1) = -(x (n + 1) + x n))
  (h₂ : ∀ n, x (n + 1) * y (n + 1) - x n * y n = -((x n + x (n + 1))^2 + (y n + y (n + 1))^2))
  (h₃ : 0 < x 0)
  (h₄ : 0 < y 0)
  (h₅ : x 0 * y 0 = 2006^2 + 1)
  : ∀ n, |x n| ≤ √2007 ∧ |x n * y n| ≤ 2007 := by
  exfalso
  have h20 : x 1 * y 1 - x 0 * y 0 = -((x 0 + x 1)^2 + (y 0 + y 1)^2) := h₂ 0
  have h21 : x 2 * y 2 - x 1 * y 1 = -((x 1 + x 2)^2 + (y 1 + y 2)^2) := h₂ 1
  have h00 : x 2 - x 1 = -(y 1 + y 0) := h₀ 0
  have h10 : y 2 - y 1 = -(x 1 + x 0) := h₁ 0
  have hx2 : x 2 = x 1 - (y 1 + y 0) := by linarith
  have hy2 : y 2 = y 1 - (x 1 + x 0) := by linarith
  rw [hx2, hy2] at h21
  nlinarith [sq_nonneg (x 0 + y 0), sq_nonneg (x 1 + y 1), sq_nonneg (x 0 - y 0),
    sq_nonneg (8 * (x 1 - y 1) + 3 * (x 0 - y 0)), mul_pos (add_pos h₃ h₄) (add_pos h₃ h₄)]
