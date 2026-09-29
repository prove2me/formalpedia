-- Prove2me | Theorems.Thm_MarkovChainCLT_summable_covariance_of_bounded_of_summable_alpha
-- name    : MarkovChainCLT.summable_covariance_of_bounded_of_summable_alpha
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-04T23:22:05.835308+00:00
-- url     : https://prove2.me/theorems/78defd08-1c55-4afb-8e67-d5e8d935942b
-- title:
--   Bounded sequence with summable $\alpha$ has absolutely summable autocovariances
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real-valued sequence on a probability space $(\Omega,\mathcal F,P)$, uniformly bounded in the sense that for some constant $B$, $|Y_n|<B$ almost surely for every $n$. Write $\alpha(n)$ for the strong mixing coefficient of the sequence at lag $n$. If
--
--   $$
--   \sum_{n\ge 0}\alpha(n)<\infty,
--   $$
--
--   then the positive-lag autocovariance series is absolutely convergent:
--
--   $$
--   \sum_{k\ge 1}\left|E[Y_0Y_k]\right|<\infty.
--   $$
--
--   This isolates the covariance-control component of the bounded case of the Ibragimov–Linnik central limit theorem (Jones, Theorem 5, condition 1): it is what makes the asymptotic-variance series $\sigma^2=E[Y_0^2]+2\sum_{k\ge 1}E[Y_0Y_k]$ well defined. The classical route is the covariance inequality for bounded strongly mixing pairs, whose lag-$k$ bound is a constant multiple of $\alpha(k)B^2$.
--
--   **Formalization Note** Positive lags are indexed as $k+1$ for $k\in\mathbb N$, and real summability is unconditional, hence equivalent to absolute convergence. The bound is stated almost surely for each time index separately.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5, condition 1 (arXiv v2 p. 9); originals: I. A. Ibragimov, Theory Probab. Appl. 7 (1962); I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Ch. 18

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory

/-- The covariance-control component of the Ibragimov–Linnik bounded-case CLT. -/
theorem MarkovChainCLT.summable_covariance_of_bounded_of_summable_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by sorry
