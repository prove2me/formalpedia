-- Prove2me | Theorems.Thm_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum
-- name    : MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T07:32:47.576757+00:00
-- url     : https://prove2.me/theorems/b3c281f4-ba0b-4f84-9d75-3b13cb616318
-- title:
--   Variance asymptotics: $n^{-1}E[S_n^2]\to\sigma^2$
-- statement:
--   Let $Y=(Y_i)_{i\ge0}$ be a measurable, strictly stationary real sequence on a probability space with $Y_0\in L^2$, write $S_n=\sum_{i<n}Y_i$ and $\gamma_k=E[Y_0Y_k]$, and assume that the positive-lag autocovariance series $\sum_{k\ge1}\gamma_k$ converges. Then the variance of the partial sums grows linearly, with slope the asymptotic variance:
--
--   $$\frac1n\,E\bigl[S_n^2\bigr]\ \longrightarrow\ \sigma^2 = \gamma_0 + 2\sum_{k\ge1}\gamma_k .$$
--
--   This is the standard variance asymptotics underlying every central limit theorem for stationary sequences: it is what identifies the limiting Gaussian variance and, when $\sigma^2>0$, what makes the two natural normalizations $\sqrt n$ and $\sqrt{E[S_n^2]}$ interchangeable.
--
--   Stationarity gives $E[Y_iY_{i+k}]=\gamma_k$, so expanding the square yields $E[S_n^2]=n\gamma_0+2\sum_{k=1}^{n-1}(n-k)\gamma_k$, and after dividing by $n$ the weights $1-k/n$ increase to $1$ while being dominated by the summable sequence $|\gamma_k|$.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n=Y_0+\dots+Y_{n-1}$; the asymptotic variance is the platform's `seqAsymptoticVariance`, namely $E[Y_0^2]+2\sum_{k\ge0}E[Y_0Y_{k+1}]$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 4 (the variance sigma^2 of Theorems 5-8, eq. (12)); the identity E[S_n^2] = n gamma_0 + 2 sum_{k<n} (n-k) gamma_k with Cesaro passage to the limit is classical, see P. Billingsley, Probability and Measure, 3rd ed. (1995), Section 27.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.tendsto_inv_mul_integral_sq_partialSum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop
      (𝓝 (seqAsymptoticVariance P Y)) := by sorry
