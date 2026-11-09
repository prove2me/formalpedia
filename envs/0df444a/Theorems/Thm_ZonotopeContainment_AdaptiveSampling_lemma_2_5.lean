-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_5
-- name    : ZonotopeContainment.AdaptiveSampling.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:46.770393+00:00
-- url     : https://prove2.me/theorems/a9e490c1-8709-4cb6-9fd3-2521aebce597
-- title:
--   Lemma 2.5 — shifted Gaussian clipping estimates
-- statement:
--   Let $N$ have the standard real Gaussian law, let $Y=m+\sigma N$, and assume $m\ge0$, $0\le\sigma\le1$ and $L\ge1$. For $q(t)=1/\max\{1,|t|\}$, both inequalities hold:
--   $$m\,\mathbb E[q(Y/L)]\le2\mathbb E[Yq(Y/L)],\qquad \mathbb E[1-q(Y/L)]\le\frac{1+\mathbb E[Yq(Y/L)]}{L}.$$
--   The statement includes the deterministic case $\sigma=0$. These scalar estimates supply the expectation bounds used in Lemma 2.4.
--
--   Differences from the source:
--   - encoding: expectations under Y = m + σN → integrals of the composed functions against gaussianReal 0 1; reason: this is the expectation under the stated Gaussian law, including the degenerate case σ = 0
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Lemma 2.5, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- Lemma 2.5, p. 9: both inequalities, including σ = 0. -/
theorem lemma_2_5 (m σ L : ℝ) (hm : 0 ≤ m) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hL : 1 ≤ L) :
    m * (∫ x : ℝ, q ((m + σ * x) / L) ∂gaussianReal 0 1) ≤
      2 * (∫ x : ℝ, (m + σ * x) * q ((m + σ * x) / L) ∂gaussianReal 0 1) ∧
    (∫ x : ℝ, 1 - q ((m + σ * x) / L) ∂gaussianReal 0 1) ≤
      (1 + ∫ x : ℝ, (m + σ * x) * q ((m + σ * x) / L) ∂gaussianReal 0 1) / L := by sorry

end ZonotopeContainment.AdaptiveSampling
