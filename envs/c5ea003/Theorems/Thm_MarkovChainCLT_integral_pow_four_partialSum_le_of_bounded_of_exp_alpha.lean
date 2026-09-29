-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_pow_four_partialSum_le_of_bounded_of_exp_alpha
-- name    : MarkovChainCLT.integral_pow_four_partialSum_le_of_bounded_of_exp_alpha
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T10:53:37.199185+00:00
-- url     : https://prove2.me/theorems/c0017ca3-faab-4f66-9089-f2008e8da9b2
-- title:
--   Fourth-moment inequality $E[S_n^4]\\le K n^2$ for bounded exponentially mixing sequences
-- statement:
--   Let $X=(X_i)_{i\ge0}$ be a measurable, centered, strictly stationary real sequence on a probability space, uniformly bounded, $|X_i|\le M$ everywhere, and with strong mixing coefficients decaying exponentially, $\alpha(n)\le c\,a^{n}$ with $0\le a<1$. Then the partial sums $S_n=\sum_{i<n}X_i$ satisfy a fourth-moment bound of the same order as in the independent case: there is a constant $K\ge0$, depending only on the law of the sequence, with
--
--   $$E\bigl[S_n^4\bigr]\ \le\ K\,n^{2}\qquad\text{for all }n .$$
--
--   This is Ibragimov's moment inequality for strongly mixing sequences. Expanding $E[S_n^4]$ as a sum over quadruples $i\le j\le k\le l$ and splitting according to the largest of the three gaps, the covariance inequality for bounded variables bounds each term with a large outer gap by a multiple of $M^4\alpha(d)$, while the terms with a large middle gap produce, besides such an error, the products $E[X_iX_j]E[X_kX_l]$ of two covariances. Summing, the number of quadruples with largest gap $d$ is of order $n\,d^{2}$, so the mixing contribution is bounded by $n\sum_d d^{2}\alpha(d)$, which is finite for an exponential rate, and the remaining product terms are $O(n^2)$ because the covariance series converges absolutely.
--
--   The bound is the input that makes the truncated part of a partial sum bounded in $L^2$ after normalization by $E[S_n^2]\asymp\sigma^2 n$, and hence uniformly integrable.
-- source:
--   I. A. Ibragimov, Some limit theorems for stationary processes, Theory Probab. Appl. 7 (1962) 349-382; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Ch. 18 (moment inequalities for strongly mixing sequences); R. Yokoyama, Moment bounds for stationary mixing sequences, Z. Wahrsch. Verw. Gebiete 52 (1980) 45-57, Theorem 1 (E|S_n|^{2p} = O(n^p) under sum_n n^{p-1} alpha(n)^{delta/(2p+delta)} < infinity), specialized to p = 2, bounded variables and an exponential mixing rate. Used for the truncated part in the proof of Theorem 6 of G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.integral_pow_four_partialSum_le_of_bounded_of_exp_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, Measurable (X n)) (hstat : IsStrictlyStationary P X)
    (hcent : ∫ ω, X 0 ω ∂P = 0)
    (M : ℝ) (hM : ∀ i, ∀ ω, |X i ω| ≤ M)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P X n ≤ c * a ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n, X i ω) ^ 4 ∂P ≤ K * (n : ℝ) ^ 2 := by sorry
