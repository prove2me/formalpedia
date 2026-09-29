-- Prove2me | Theorems.Thm_BanditAlgorithm_lintegral_gaussian_mixture_exp_tilt_pair
-- name    : BanditAlgorithm.lintegral_gaussian_mixture_exp_tilt_pair
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:29:40.269594+00:00
-- url     : https://prove2.me/theorems/91ffb26b-8309-4502-9b6d-f411c0cbe795
-- title:
--   The planar Gaussian mixture of a pair of exponential tilts
-- statement:
--   The two-dimensional method of mixtures: for $s,t\ge0$ and $y,z\in\mathbb R$, integrating a pair of independent exponential tilts against the standard Gaussian density of the plane gives
--   $$\int_{\mathbb R^2}\varphi(\lambda_1)\varphi(\lambda_2)\,e^{\lambda_1 y-\lambda_1^2 s/2}\,e^{\lambda_2 z-\lambda_2^2 t/2}\,d\lambda=\frac{1}{\sqrt{1+s}}e^{\frac{y^2}{2(1+s)}}\cdot\frac{1}{\sqrt{1+t}}e^{\frac{z^2}{2(1+t)}},$$
--   where $\varphi$ is the standard Gaussian density.
--
--   The statistic of Chernoff's stopping rule compares the threshold against a *pair* of arms at a time, so the martingale controlling it mixes over a tilt supported on two coordinates, and this is the resulting weight. The two prefactors $(1+s)^{-1/2}$, $(1+t)^{-1/2}$ are the source of the polynomial term in the threshold $f(x)=e^{k-x}(x/k)^k$ of Lattimore--Szepesv\'ari Lemma 33.7.
-- source:
--   Standard Gaussian mixture computation in two coordinates (Kaufmann & Koolen, Mixture martingales revisited, JMLR 22, 2021, Section 3). The two-arm case is what the pairwise statistic of Chernoff's stopping rule requires.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Real

theorem BanditAlgorithm.lintegral_gaussian_mixture_exp_tilt_pair {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (y z : ℝ) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
        (((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(p.1 ^ 2) / 2)
            * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(p.2 ^ 2) / 2)))
          * Real.exp ((p.1 * y - p.1 ^ 2 * s / 2) + (p.2 * z - p.2 ^ 2 * t / 2)))
      = ENNReal.ofReal ((Real.sqrt (1 + s))⁻¹ * Real.exp (y ^ 2 / (2 * (1 + s))))
        * ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) := by
  sorry
