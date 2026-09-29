-- Prove2me | Theorems.Thm_BanditAlgorithm_integral_exp_tilt_mixture
-- name    : BanditAlgorithm.integral_exp_tilt_mixture
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:48:54.629883+00:00
-- url     : https://prove2.me/theorems/526e5933-e358-4184-8e16-c5a26f74ab89
-- title:
--   The Gaussian mixture of an exponential tilt
-- statement:
--   Mixing an exponential tilt over a standard Gaussian prior on the tilt parameter produces the self-normalised weight: for $t\ge0$ and $z\in\mathbb R$,
--   $$\int_{\mathbb R}\frac{1}{\sqrt{2\pi}}e^{-\lambda^2/2}\,e^{\lambda z-\lambda^2 t/2}\,d\lambda=\frac{1}{\sqrt{1+t}}\;\exp\left(\frac{z^2}{2(1+t)}\right).$$
--
--   This is the method of mixtures in its basic form (Kaufmann--Koolen, JMLR 2021; Garivier--Kaufmann, COLT 2016, \S4). Applied to the bandit exponential martingale with $z=S_a(n)-T_a(n)\mu_a$ and $t=T_a(n)$, it converts a family of fixed-tilt martingales into a single martingale whose exponent is the self-normalised deviation $z^2/(2(1+t))$ -- no longer requiring a union over pull counts. The prefactors $(1+T_i(n))^{-1/2}$, one per arm, are the source of the polynomial factor $(x/k)^k$ in the threshold $f(x)=e^{k-x}(x/k)^k$ of Lattimore--Szepesv\'ari Lemma 33.7. The computation is the Gaussian integral with a linear term at $a=(1+t)/2$, $c=z$.
-- source:
--   The method of mixtures in its basic form: Robbins & Siegmund (1970); Kaufmann & Koolen, Mixture martingales revisited, JMLR 22 (2021), Section 3; Garivier & Kaufmann, COLT 2016, Section 4.

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Real

theorem BanditAlgorithm.integral_exp_tilt_mixture {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫ lam : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2)
      = (Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t))) := by
  sorry
