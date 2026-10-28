-- Prove2me | Theorems.Thm_HarmonicBuilding_weakly_subharmonic_mean_value_ineq
-- name    : HarmonicBuilding.weakly_subharmonic_mean_value_ineq
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T06:33:16.02772+00:00
-- url     : https://prove2.me/theorems/622817dd-fba5-4f93-b874-878ea813fb93
-- title:
--   Mean value inequality for continuous nonnegative weakly subharmonic functions on $\mathbb C$
-- statement:
--   There is a constant $C>0$ with the following property. Let $f:\mathbb C\to\mathbb R$ be continuous and nonnegative, $x\in\mathbb C$, $\rho_0>0$, and suppose $\int f\,\Delta\eta\ge0$ for every nonnegative $\eta\in C^2(\mathbb C)$ vanishing outside some ball $B(x,\rho_1)$ with $\rho_1<\rho_0$. Then for all $0<\rho<\rho_0$,
--
--   $$f(x)\le \frac{C}{\rho^2}\int_{B(x,\rho)} f(z)\,dz .$$
--
--   Role: the mean value inequality applied to $d^2(u,u(\cdot+v))$ in the Lipschitz regularity of the minimizer.
-- source:
--   Gilbarg and Trudinger, Elliptic Partial Differential Equations of Second Order, Springer (2001), Theorem 2.1 (mean value inequality for subharmonic functions), https://doi.org/10.1007/978-3-642-61798-0

import Mathlib
open Set MeasureTheory Filter
open scoped Manifold NNReal

namespace HarmonicBuilding

theorem weakly_subharmonic_mean_value_ineq :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℂ) (f : ℂ → ℝ), Continuous f → (∀ z, 0 ≤ f z) →
      ∀ ρ₀ : ℝ, (∀ η : ℂ → ℝ, ContDiff ℝ 2 η → (∀ z, 0 ≤ η z) →
        (∃ ρ₁ < ρ₀, ∀ z, ρ₁ ≤ dist z x → η z = 0) →
        0 ≤ ∫ z, f z * Laplacian.laplacian η z) →
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → f x ≤ C / ρ ^ 2 * ∫ z in Metric.ball x ρ, f z := by sorry

end HarmonicBuilding
