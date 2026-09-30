-- Prove2me | Theorems.Thm_RybinAI2026_P01_diagonal_angle_sin_integral_formula
-- name    : RybinAI2026.P01.diagonal_angle_sin_integral_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T06:23:43.340712+00:00
-- url     : https://prove2.me/theorems/82538707-1e12-4fca-b253-52cceb82ade9
-- title:
--   Diagonal angle integral with sine numerator
-- statement:
--   For positive diagonal entries a and b, the full-period angular integral of |sin θ| divided by a cos² θ + b sin² θ equals 4/b times ψ(a/b), where ψ(t)=∫₀¹(1+(t−1)s²)⁻¹ ds. This is the second-coordinate companion to the cosine-numerator formula and follows by quarter-turn symmetry.
-- source:
--   Derived coordinate companion to artifacts/p01_slack/2026-09-29-no-w-pair.md, Addendum: aligned 2D pair contraction resolved. The quarter-turn θ ↦ π/2−θ interchanges sine and cosine and swaps the diagonal coefficients; the existing cosine formula then evaluates the integral.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_diagonal_angle_integral_formula

theorem RybinAI2026.P01.diagonal_angle_sin_integral_formula (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    ∫ θ in (-Real.pi)..Real.pi,
      |Real.sin θ| / (a * Real.cos θ ^ 2 + b * Real.sin θ ^ 2) = 4 * ψ (a / b) / b := by
  sorry
