-- Prove2me | Theorems.Thm_RybinAI2026_P01_sq_le_mul_of_quadratic_nonneg
-- name    : RybinAI2026.P01.sq_le_mul_of_quadratic_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T00:24:02.867708+00:00
-- url     : https://prove2.me/theorems/7d86a820-788b-4536-991b-4453f90b5f85
-- title:
--   Positive quadratic in lambda bounds the middle coefficient
-- statement:
--   For real A, B, D with B, D nonnegative, if the quadratic form A - 2 λ B + λ² D is nonnegative for every real λ, then B² ≤ A·D.  Evaluated at λ = B/D (when D > 0) this is the discriminant condition; when D = 0 the coefficient B must vanish, since otherwise a suitable λ makes the expression negative.
-- source:
--   P01 mission c36fd4df-ef29-4fbc-9bb6-1f6acf3c0733, root 8d67c9ac-a6c7-418c-b8db-0bc029c18484. Pure-real core of the Cauchy-Schwarz input of one_sphere_cross_excess_cauchy_schwarz (bbefa105); see artifacts/p01_slack/2026-10-03-two-point-reformulation.md.

import Mathlib

namespace RybinAI2026.P01

/-- Discriminant form of the positivity of a real quadratic in lambda. -/
theorem sq_le_mul_of_quadratic_nonneg {A B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (h : ∀ lam : ℝ, 0 ≤ A - 2 * lam * B + lam ^ 2 * D) : B ^ 2 ≤ A * D := by sorry

end RybinAI2026.P01
