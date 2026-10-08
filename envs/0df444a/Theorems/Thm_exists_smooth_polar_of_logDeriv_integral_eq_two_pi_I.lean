-- Prove2me | Theorems.Thm_exists_smooth_polar_of_logDeriv_integral_eq_two_pi_I
-- name    : exists_smooth_polar_of_logDeriv_integral_eq_two_pi_I
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T19:02:25.068355+00:00
-- url     : https://prove2.me/theorems/0f055ec2-e610-4b8f-8d01-60fad261c737
-- title:
--   Smooth polar form of a loop with winding number one
-- statement:
--   Let $c:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be smooth and $1$-periodic with $\int_0^1 c'/c=2\pi i$. Then there are smooth $r,\theta:\mathbb{R}\to\mathbb{R}$ with $r>0$ and $1$-periodic, $\theta(s+1)=\theta(s)+2\pi$, and $c=r\,e^{i\theta}$.
--   Take $L(s)=\int_0^s c'/c$. Then $c=c(0)e^{L}$, so $r=|c(0)|e^{\operatorname{Re}L}$ and $\theta=\arg c(0)+\operatorname{Im}L$ work.
-- source:
--   Standard winding-number calculus for C^1 loops in C \ {0}; used for the conormal winding of a disk-like global surface of section in Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 1.7 (via Hryniewicz, Trans. AMS 364 (2012), Prop. 2.1).

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

open scoped ContDiff

theorem exists_smooth_polar_of_logDeriv_integral_eq_two_pi_I {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hne : ∀ s, c s ≠ 0)
    (hper : ∀ s, c (s + 1) = c s)
    (hW : ∫ s in (0 : ℝ)..1, deriv c s / c s = 2 * Real.pi * Complex.I) :
    ∃ r θ : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ContDiff ℝ ∞ θ ∧ (∀ s, 0 < r s) ∧
      (∀ s, r (s + 1) = r s) ∧ (∀ s, θ (s + 1) = θ s + 2 * Real.pi) ∧
      ∀ s, c s = (r s : ℂ) * (Real.cos (θ s) + Real.sin (θ s) * Complex.I) := by sorry
