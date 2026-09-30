-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_angle_integral_formula
-- name    : RybinAI2026.P01.diagonal_angle_integral_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T05:13:11.732241+00:00
-- url     : https://prove2.me/theorems/c2bb123b-6132-4ca9-ac20-3b24657e379f
-- title:
--   Scalar angle integral for a diagonal quadratic form
-- statement:
--   For positive a and b, integrating |cos(theta)| divided by the diagonal quadratic form a cos(theta)^2 + b sin(theta)^2 over one full angular period gives 4/a times psi(b/a), where psi(t)=integral_0^1 (1+(t-1)s^2)^(-1) ds.
-- source:
--   The exact diagonal 2D integral formula recorded in artifacts/p01_slack/2026-09-29-no-w-pair.md. Periodicity and first-quadrant substitution reduce it to the paper's psi integral; this is the scalar-calculus leaf needed after converting the P01 sphere integral to angular coordinates.

import Mathlib

theorem RybinAI2026.P01.diagonal_angle_integral_formula (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    ∫ θ in (-Real.pi)..Real.pi,
      |Real.cos θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) = 4 * ψ (b / a) / a := by
  sorry
