-- Prove2me | Theorems.Thm_MarkovChainCLT_summable_covariance_of_exp_alpha_of_log_moment
-- name    : MarkovChainCLT.summable_covariance_of_exp_alpha_of_log_moment
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-04T23:43:23.862048+00:00
-- url     : https://prove2.me/theorems/6b1c16dc-edb2-4617-b47b-c6b7808e3249
-- title:
--   Exponential $\alpha$-mixing with a $Y^2\log^+|Y|$ moment gives absolutely summable autocovariances
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real-valued sequence on a probability space $(\Omega,\mathcal F,P)$ whose strong mixing coefficients decay exponentially, $\alpha(n)\le c\,a^n$ for some constant $c$ and some $0\le a<1$, and which satisfies the moment condition
--
--   $$
--   E\bigl[Y_0^2\log^+|Y_0|\bigr]<\infty,\qquad \log^+t=\max(0,\log t).
--   $$
--
--   Then the positive-lag autocovariance series is absolutely convergent:
--
--   $$
--   \sum_{k\ge 1}\left|E[Y_0Y_k]\right|<\infty.
--   $$
--
--   This isolates the covariance-control component of the Doukhan–Massart–Rio central limit theorem (Jones, Theorem 6): it is what makes the asymptotic-variance series $\sigma^2=E[Y_0^2]+2\sum_{k\ge 1}E[Y_0Y_k]$ well defined. In the source the bound comes from Rio's covariance inequality in terms of the quantile function of $|Y_0|$ and the mixing rate, for which the $Y^2\log^+|Y|$ moment together with exponential decay of $\alpha$ is exactly the summability condition.
--
--   **Formalization Note** Positive lags are indexed as $k+1$ for $k\in\mathbb N$, and real summability is unconditional, hence equivalent to absolute convergence. The stated moment already implies $E[Y_0^2]<\infty$, so square-integrability is not assumed separately.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 6 (arXiv v2 p. 11); original: P. Doukhan, P. Massart and E. Rio, The functional central limit theorem for strongly mixing processes, Ann. Inst. H. Poincaré Probab. Statist. 30 (1994) 63-82 (special case)

import Definitions.Def_MixingCoefficients
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory

/-- The covariance-control component of the Doukhan–Massart–Rio CLT. -/
theorem MarkovChainCLT.summable_covariance_of_exp_alpha_of_log_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by sorry
