-- Prove2me | Theorems.Thm_BanditAlgorithm_klDiv_gaussianReal_same_variance
-- name    : BanditAlgorithm.klDiv_gaussianReal_same_variance
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:21:09.663153+00:00
-- url     : https://prove2.me/theorems/bf9a5a6a-7b06-4bac-a759-45881c0292e4
-- title:
--   KL divergence between two real Gaussians of equal variance
-- statement:
--   The Kullback--Leibler divergence between two Gaussians of the same variance $v>0$ is
--   $$D\bigl(\mathcal N(a,v)\,\Vert\,\mathcal N(b,v)\bigr)=\frac{(a-b)^2}{2v}.$$
--
--   This closed form is absent from Mathlib and is the arithmetic backbone of the whole Gaussian best-arm-identification chapter: it turns the information-theoretic characteristic time $c^*(\nu)^{-1}=\sup_\alpha\inf_{\nu'}\sum_i\alpha_i D(\nu_i\Vert\nu_i')$ into the quadratic optimisation over means that Lattimore--Szepesv\'ari solve in closed form. The proof computes the log-likelihood ratio $\log\frac{d\mathcal N(a,v)}{d\mathcal N(b,v)}(x)$, which is affine in $x$, so only the first moment of $\mathcal N(a,v)$ is needed.
-- source:
--   Standard; see e.g. Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Section 33.1 (the Gaussian class E^k_N(1)), and Cover & Thomas, Elements of Information Theory, Chapter 8.

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

theorem BanditAlgorithm.klDiv_gaussianReal_same_variance {v : NNReal} (hv : v ≠ 0) (a b : ℝ) :
    InformationTheory.klDiv (ProbabilityTheory.gaussianReal a v)
        (ProbabilityTheory.gaussianReal b v)
      = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  sorry
