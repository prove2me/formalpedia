-- Prove2me | Theorems.Thm_Statistics_cramer_rao_quadratic_le_variance
-- name    : Statistics.cramer_rao_quadratic_le_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T23:54:53.475064+00:00
-- url     : https://prove2.me/theorems/e75412a7-f6ff-4443-b60a-ace09e6b52fe
-- title:
--   Constrained Cramér–Rao bound: $y^\top I y \le \mathrm{Var}(\delta)$
-- statement:
--   **The constrained Cramér–Rao bound in quadratic form**, stated so that no matrix has to be inverted. Let $\mu$ be a probability measure, $\delta \in L^2(\mu)$ a statistic, and $(g_i)_{i \in \iota}$ a finite family of centred scores in $L^2(\mu)$ with Fisher (Gram) matrix $I_{ij} = \mathbb{E}_\mu[g_i g_j]$. Suppose the vector of covariances of $\delta$ with the scores lies in the range of $I$, with $y$ a solution of the normal equations:
--   $$\mathbb{E}_\mu[\delta\, g_i] \;=\; (Iy)_i \quad \text{for all } i.$$
--   Then
--   $$y^\top I y \;\le\; \operatorname{Var}_\mu(\delta).$$
--   In a differentiable model the left-hand side is exactly the constrained Cramér–Rao bound: if $\nabla_\theta \mathbb{E}_\theta[\delta] = \nabla g(\theta)$ then $y$ solves $Iy = \nabla g$ and $y^\top I y = \nabla g^\top I^{+} \nabla g$, the bound of Stoica–Ng and Moore, with $I^{+}$ the Moore–Penrose pseudo-inverse. Working with $y$ rather than $I^{+}$ makes the statement meaningful for singular $I$ — the situation that arises whenever the parameter is constrained, e.g. to a probability simplex — and the proof is the one-dimensional information inequality applied to the single score $G = \sum_i y_i g_i$, for which $\mathbb{E}_\mu[\delta G] = \mathbb{E}_\mu[G^2] = y^\top I y$.
-- source:
--   P. Stoica and B. C. Ng, On the Cramér-Rao bound under parametric constraints, IEEE Signal Processing Letters 5(7) (1998), 177-179, Theorem 1; T. J. Moore, A theory of Cramér-Rao bounds for constrained parametric models, PhD thesis, University of Maryland, 2010, Corollary 3.10. Both are quoted as Lemma EC.8 and Lemma EC.9 of H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.8.3.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped ENNReal NNReal

theorem Statistics.cramer_rao_quadratic_le_variance {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (δ : Ω → ℝ) (hδ : MemLp δ 2 μ)
    (g : ι → Ω → ℝ) (hg : ∀ i, MemLp (g i) 2 μ) (hg0 : ∀ i, ∫ ω, g i ω ∂μ = 0)
    (I : ι → ι → ℝ) (hI : ∀ i j, I i j = ∫ ω, g i ω * g j ω ∂μ)
    (y : ι → ℝ) (hy : ∀ i, ∫ ω, δ ω * g i ω ∂μ = ∑ j, I i j * y j) :
    ∑ i, ∑ j, y i * I i j * y j ≤ ∫ ω, (δ ω - ∫ ω', δ ω' ∂μ) ^ 2 ∂μ := by sorry
