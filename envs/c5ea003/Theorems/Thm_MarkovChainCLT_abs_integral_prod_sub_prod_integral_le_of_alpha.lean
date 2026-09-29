-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_integral_prod_sub_prod_integral_le_of_alpha
-- name    : MarkovChainCLT.abs_integral_prod_sub_prod_integral_le_of_alpha
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T09:04:17.6519+00:00
-- url     : https://prove2.me/theorems/b9221a22-0a2e-4016-87dc-793f0109929d
-- title:
--   Ibragimov's block-independence lemma: $\|E[\prod_j f_j]-\prod_j E[f_j]\|\le 16(m-1)\alpha(n)\prod_j M_j$
-- statement:
--   Let $Y=(Y_i)_{i\ge0}$ be a measurable process on a probability space $(\Omega,\mathcal F,P)$ with strong mixing coefficients $\alpha(n)$. Consider $m$ blocks of time indices
--
--   $$[a_0,b_0],\,[a_1,b_1],\,\dots,\,[a_{m-1},b_{m-1}],$$
--
--   separated by gaps of length at least $n$, that is $b_j+n\le a_{j+1}$ for every $j$, and let $f_j$ be a complex random variable measurable with respect to $\sigma(Y_i: a_j\le i\le b_j)$ with $\|f_j\|_\infty\le M_j$. Then the expectation of the product factorizes up to an error of $16\alpha(n)$ per junction:
--
--   $$\Bigl\|\,E\Bigl[\prod_{j<m}f_j\Bigr]-\prod_{j<m}E[f_j]\,\Bigr\|\;\le\;16\,(m-1)\,\alpha(n)\prod_{j<m}M_j.$$
--
--   This is Ibragimov's block-independence lemma, the combinatorial heart of every characteristic-function proof of a central limit theorem for mixing sequences. Taking $f_j=\exp(\mathrm{i}t\,S_j)$, where $S_j$ is the sum of the observations in the $j$-th block (so $M_j=1$), it says that the characteristic function of a sum of well-separated big blocks differs from that of independent blocks by at most $16(m-1)\alpha(n)$. In the Bernstein big-block/small-block scheme the number of blocks $m$ grows with the sample size while the gap $n$ grows fast enough that $m\,\alpha(n)\to0$, which is precisely how a mixing-rate hypothesis such as $\sum_n\alpha(n)^{\delta/(2+\delta)}<\infty$ or $\alpha(n)=O(a^n)$ enters the proof.
--
--   The bound follows from the two-block case, the covariance inequality $|E[UV]-E[U]E[V]|\le16\|U\|_\infty\|V\|_\infty\alpha(n)$ for bounded complex variables measurable with respect to a past and a future separated by $n$, applied once at each of the $m-1$ junctions.
--
--   **Formalization Note** The block schedule is given by two sequences $a,b:\mathbb N\to\mathbb N$ and the hypotheses constrain only the indices actually used, $j<m$; blocks are allowed to be arbitrary index intervals rather than consecutive runs. For $m=0$ and $m=1$ both sides are $0$, so the statement is trivially true there and the constant $m-1$ is a truncated natural subtraction. Boundedness is stated pointwise.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (Wolters-Noordhoff, 1971), Lemma 17.2.1 and Theorem 18.5.3 (the block factorization of characteristic functions under strong mixing); R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144, Theorem 4.4 and the discussion of the Bernstein blocking argument.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.abs_integral_prod_sub_prod_integral_le_of_alpha {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hY : ∀ i, Measurable (Y i)) (n : ℕ) (a b : ℕ → ℕ) (f : ℕ → Ω → ℂ)
    (M : ℕ → ℝ) (m : ℕ)
    (hab : ∀ j, j < m → a j ≤ b j)
    (hgap : ∀ j, j + 1 < m → b j + n ≤ a (j + 1))
    (hf : ∀ j, j < m → Measurable[processSigma Y (Set.Icc (a j) (b j))] (f j))
    (hM : ∀ j, j < m → 0 ≤ M j)
    (hfb : ∀ j, j < m → ∀ ω, ‖f j ω‖ ≤ M j) :
    ‖(∫ ω, ∏ j ∈ Finset.range m, f j ω ∂P) - ∏ j ∈ Finset.range m, ∫ ω, f j ω ∂P‖
      ≤ 16 * ((m - 1 : ℕ) : ℝ) * alphaMixingCoef P Y n * ∏ j ∈ Finset.range m, M j := by sorry
