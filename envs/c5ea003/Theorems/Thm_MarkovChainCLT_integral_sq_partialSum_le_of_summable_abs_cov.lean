-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_partialSum_le_of_summable_abs_cov
-- name    : MarkovChainCLT.integral_sq_partialSum_le_of_summable_abs_cov
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T12:33:14.217361+00:00
-- url     : https://prove2.me/theorems/78760bc3-dcc4-4402-8b58-fc79059f5278
-- title:
--   $E[S_n^2] \le n\,(E[Y_0^2] + 2\sum_k |E[Y_0Y_k]|)$ for a stationary sequence
-- statement:
--   **A linear bound on the second moment of the partial sums, valid for every $n$.**
--
--   Let $Y=(Y_n)_{n\ge0}$ be a measurable, strictly stationary real sequence on a probability space with $Y_0\in L^2$, and suppose its autocovariances $\gamma_k = E[Y_0Y_k]$ are *absolutely* summable, $\sum_{k\ge1}|\gamma_k|<\infty$. Then, with $S_n=\sum_{i<n}Y_i$,
--
--   $$E[S_n^2]\;\le\; n\Bigl(E[Y_0^2] + 2\sum_{k\ge1}|\gamma_k|\Bigr)\qquad\text{for every } n .$$
--
--   Expanding the square and using stationarity, $E[Y_iY_j]$ depends only on $|i-j|$, so
--
--   $$E[S_n^2] \;=\; n\,\gamma_0 + 2\sum_{k=1}^{n-1}(n-k)\,\gamma_k,$$
--
--   and each weight satisfies $0\le n-k\le n$; replacing $\gamma_k$ by $|\gamma_k|$ and the partial sum by the whole series gives the bound.
--
--   **Role.** The asymptotic statement $n^{-1}E[S_n^2]\to\sigma^2$ is the one that identifies the limiting variance, but a blocking argument needs a bound that is uniform in $n$ with an explicit constant: it controls the variance of *every* block by a fixed multiple of the block length, in particular for the short blocks whose total contribution must be shown negligible in Bernstein's big-block/small-block decomposition. For a bounded sequence with summable strong mixing coefficients the hypothesis of absolute summability is automatic, since $|\gamma_k|\le 4B^2\alpha(k)$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Section 4 (the variance sigma^2 = E[Y_0^2] + 2 sum_k E[Y_0 Y_k] of Theorems 5-8); the elementary expansion E[S_n^2] = n gamma_0 + 2 sum_{k<n} (n-k) gamma_k of the second moment of the partial sums of a stationary sequence is standard, see e.g. I. A. Ibragimov & Yu. V. Linnik, "Independent and Stationary Sequences of Random Variables" (1971), Ch. 18.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.integral_sq_partialSum_le_of_summable_abs_cov {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable fun k : ℕ => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
      ≤ (n : ℝ) * ((∫ ω, Y 0 ω ^ 2 ∂P)
          + 2 * ∑' k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) := by sorry
