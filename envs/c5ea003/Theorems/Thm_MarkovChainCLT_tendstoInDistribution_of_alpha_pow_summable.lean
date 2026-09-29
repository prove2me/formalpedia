-- Prove2me | Theorems.Thm_MarkovChainCLT_tendstoInDistribution_of_alpha_pow_summable
-- name    : MarkovChainCLT.tendstoInDistribution_of_alpha_pow_summable
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-04T23:08:57.467797+00:00
-- url     : https://prove2.me/theorems/39805139-f9e7-44dc-9de7-f6d6c43aec76
-- title:
--   Distributional limit for a strongly mixing stationary sequence with a $2+\delta$ moment
-- statement:
--   Let $Y=(Y_n)_{n\ge 0}$ be a measurable, centered, strictly stationary real-valued sequence on a probability space $(\Omega,\mathcal F,P)$, with $E|Y_0|^{2+\delta}<\infty$ for some $\delta>0$ and strong mixing coefficients satisfying $\sum_{n\ge 0}\alpha(n)^{\delta/(2+\delta)}<\infty$. Assume also that the positive-lag autocovariance series $\sum_{k\ge 1}E[Y_0Y_k]$ is absolutely convergent, and define
--
--   $$
--   \sigma^2=E[Y_0^2]+2\sum_{k\ge 1}E[Y_0Y_k].
--   $$
--
--   If $\sigma^2>0$, then the normalized partial sums obey
--
--   $$
--   \frac{1}{\sqrt n}\sum_{i=0}^{n-1}Y_i\xrightarrow{d}N(0,\sigma^2).
--   $$
--
--   This isolates the blocking and distributional-limit component of the moment case of the Ibragimov–Linnik central limit theorem (Jones, Theorem 5, condition 2), after covariance convergence has been established separately.
--
--   **Formalization Note** Convergence is weak convergence of the laws under the common probability measure $P$; the Gaussian variance is represented by the nonnegative-real coercion of $\sigma^2$, which equals $\sigma^2$ under the positivity hypothesis.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 5, condition 2, eq. (10) (arXiv v2 p. 9); originals: I. A. Ibragimov, Theory Probab. Appl. 7 (1962); I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables (1971), Theorem 18.5.3

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- The blocking/limit component of the Ibragimov–Linnik moment-case CLT, after
covariance summability has been isolated. -/
theorem MarkovChainCLT.tendstoInDistribution_of_alpha_pow_summable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ))))
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by sorry
