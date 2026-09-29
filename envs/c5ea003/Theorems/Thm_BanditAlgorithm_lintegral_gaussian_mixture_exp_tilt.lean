-- Prove2me | Theorems.Thm_BanditAlgorithm_lintegral_gaussian_mixture_exp_tilt
-- name    : BanditAlgorithm.lintegral_gaussian_mixture_exp_tilt
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:28:45.973181+00:00
-- url     : https://prove2.me/theorems/d8686689-c772-45f2-a8f3-19eef2b6a6a8
-- title:
--   The Gaussian mixture of an exponential tilt, in the extended nonnegative reals
-- statement:
--   The method of mixtures, in the $[0,\infty]$-valued form that Tonelli's theorem applies to: for $t\ge0$ and $z\in\mathbb R$,
--   $$\int_{\mathbb R}\frac{1}{\sqrt{2\pi}}e^{-\lambda^2/2}\,e^{\lambda z-\lambda^2t/2}\,d\lambda=\frac{1}{\sqrt{1+t}}\exp\left(\frac{z^2}{2(1+t)}\right).$$
--
--   The Bochner-integral version is the same computation, but every downstream use sits inside an interchange with the trajectory measure of a bandit, and Tonelli's theorem needs the integrand to be $[0,\infty]$-valued. Transporting between the two costs the integrability of the Gaussian with a linear term. Applied to the bandit exponential martingale with $z=S_a(n)-T_a(n)\mu_a$ and $t=T_a(n)$, this converts a family of fixed-tilt martingales into a single martingale whose exponent is the self-normalised deviation $z^2/(2(1+t))$.
-- source:
--   Standard Gaussian mixture computation (Robbins & Siegmund 1970; Kaufmann & Koolen, JMLR 22, 2021, Section 3). Stated in the extended nonnegative reals so that Tonelli's theorem applies inside the bandit trajectory integral.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Real

theorem BanditAlgorithm.lintegral_gaussian_mixture_exp_tilt {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫⁻ lam : ℝ, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2))
      = ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) := by
  sorry
