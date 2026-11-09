-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_lemma_2_4
-- name    : ZonotopeContainment.AdaptiveSampling.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:22:54.172077+00:00
-- url     : https://prove2.me/theorems/1ab54d8f-305c-425e-ab3e-449b1d83a970
-- title:
--   Lemma 2.4 — good updates
-- statement:
--   There is an absolute constant $c_0>0$, independent of all the following data. Let $d\ge3$, $C\ge64$, $\lambda\ge1$, let the finite family $v_i$ span $\mathbb R^d$, and let $b\ne0$. With $E$, $\mu$, $S$, $v^+$, $b^+$, $H$ and $H^+$ as defined for a local Gaussian update,
--   $$\mathbb P(E)\ge c_0\exp\left(-\frac{\log d}{C^2\lambda^2}\right),\qquad \mu>0.$$
--   Conditional on $E$, with probability at least one half, both inequalities hold:
--   $$\|b^+\|^2\le\frac{8C^2\lambda^2}{\sqrt{\log d}}\|b\|\mu,\qquad H-H^+\le\frac{4H}{C\lambda}+4\mu.$$
--   This is a one-step statement; it requires no upper Lewis bound or integrability hypothesis.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators have zero projection and matrix contribution, weight one, and stay zero; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: current generators and functional b = Aᵀa of Algorithm 1 → every spanning real generator family, every b ≠ 0 and all C ≥ 64, λ ≥ 1; reason: the local estimates use spanning and these parameter bounds, with a single uniform c₀, and do not use the upper Lewis bound; b ≠ 0 is what makes b/‖b‖ in E defined
--   - encoding: conditional probability of both good-update inequalities at least one half → the outer measure of E intersected with failure is at most P(E)/2; reason: E is measurable with positive probability; a complementary upper bound gives the same probability guarantee without relying on measurability of the good-update predicate
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Lemma 2.4 and equation (4), p. 8; E and μ on p. 7; proof pp. 9–10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_LocalGaussian

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- Lemma 2.4, p. 8: the absolute constant is uniform even in C and lam. -/
theorem lemma_2_4 : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ C lam : ℝ, 64 ≤ C → 1 ≤ lam →
    ∀ (v : Fin n → E d), Submodule.span ℝ (Set.range v) = ⊤ →
    ∀ b : E d, b ≠ 0 →
    ENNReal.ofReal (c₀ * Real.exp (-Real.log d / (C ^ 2 * lam ^ 2))) ≤
      stdGaussian (E d) (alignmentEvent C lam b) ∧
    0 < conditionalMean C lam v b ∧
    stdGaussian (E d) {z | z ∈ alignmentEvent C lam b ∧ ¬ GoodUpdate C lam v b z} ≤
      stdGaussian (E d) (alignmentEvent C lam b) / 2 := by sorry

end ZonotopeContainment.AdaptiveSampling
