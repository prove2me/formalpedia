-- Prove2me | Theorems.Thm_MarkovChainCLT_summable_covariance_of_alpha_pow_summable
-- name    : MarkovChainCLT.summable_covariance_of_alpha_pow_summable
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-04T23:08:46.772475+00:00
-- url     : https://prove2.me/theorems/8aebe2e9-e64c-43ac-a73c-d8165630aac6
-- title:
--   Summable $\alpha^{\delta/(2+\delta)}$ with a $2+\delta$ moment implies absolute autocovariance summability
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real-valued sequence on a probability space $(\Omega,\mathcal F,P)$, and suppose that for some $\delta>0$ the moment $E|Y_0|^{2+\delta}$ is finite. Write $\alpha(n)$ for the strong mixing coefficient of the sequence at lag $n$ (the supremum over $k$ of $|P(A\cap B)-P(A)P(B)|$ over $A\in\sigma(Y_0,\dots,Y_k)$ and $B\in\sigma(Y_j : j\ge k+n)$). If
--
--   $$
--   \sum_{n\ge 0}\alpha(n)^{\delta/(2+\delta)}<\infty,
--   $$
--
--   then the positive-lag autocovariance series is absolutely convergent:
--
--   $$
--   \sum_{k\ge 1}\left|E[Y_0Y_k]\right|<\infty.
--   $$
--
--   This isolates the covariance-control component of the moment case of the Ibragimov–Linnik central limit theorem (Jones, Theorem 5, condition 2): it is what makes the asymptotic-variance series $\sigma^2=E[Y_0^2]+2\sum_{k\ge 1}E[Y_0Y_k]$ well defined. The classical route is the covariance inequality for strongly mixing pairs with $2+\delta$ moments, whose lag-$k$ bound is a constant multiple of $\alpha(k)^{\delta/(2+\delta)}$.
--
--   **Formalization Note** Positive lags are indexed as $k+1$ for $k\in\mathbb N$, and real summability is unconditional, hence equivalent to absolute convergence. The moment hypothesis is stated as integrability of $|Y_0|^{2+\delta}$ with a real exponent.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5, condition 2, eq. (10) (arXiv v2 p. 9); originals: I. A. Ibragimov, Theory Probab. Appl. 7 (1962); I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Theorem 18.5.3

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory

/-- The covariance-control component of the Ibragimov–Linnik moment-case CLT. -/
theorem MarkovChainCLT.summable_covariance_of_alpha_pow_summable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by sorry
