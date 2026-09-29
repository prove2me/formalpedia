-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
-- name    : BanditAlgorithm.gaussian_relative_entropy_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-18T23:57:19.660316+00:00
-- url     : https://prove2.me/theorems/3c4fe7e7-18d0-44f3-83c7-58de5c8bc986
-- statement:
--   (Gaussian KL formula) For means $\mu_1,\mu_2 \in \mathbb{R}$ and common variance $v \ne 0$ (Mathlib's `gaussianReal` takes the VARIANCE $v : \mathbb{R}_{\ge 0}$, not the standard deviation):
--
--   $$D(\mathcal{N}(\mu_1,v), \mathcal{N}(\mu_2,v)) = \frac{(\mu_1-\mu_2)^2}{2v},$$
--
--   stated with `InformationTheory.klDiv` valued in $[0,\infty]$. The hypothesis $v \ne 0$ is required: Mathlib defines `gaussianReal μ 0 = dirac μ`, so at $v=0$ the true KL is $0$ if $\mu_1=\mu_2$ and $\infty$ otherwise, while the formula's right-hand side would be the junk value `ofReal(x/0) = 0`.
-- source:
--   L&S Ch 14.2 (specialization of Theorem 14.1), p.190

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real


open MeasureTheory ProbabilityTheory InformationTheory NNReal

theorem BanditAlgorithm.gaussian_relative_entropy_formula (μ₁ μ₂ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal μ₁ v) (gaussianReal μ₂ v) =
      ENNReal.ofReal ((μ₁ - μ₂) ^ 2 / (2 * (v : ℝ))) := by
  sorry
