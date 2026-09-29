-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_exp_alpha
-- name    : MarkovChainCLT.clt_of_var_limit_of_exp_alpha
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T08:37:18.102437+00:00
-- url     : https://prove2.me/theorems/1f9b8a97-4f2e-42bf-bdf5-9f2268e83dd3
-- title:
--   CLT for exp-mixing sequences given variance convergence
-- statement:
--   Let $Y = (Y_n)_{n \ge 0}$ be a centered strictly stationary real-valued sequence on a probability space $(\Omega, \mathcal F, P)$ with exponentially decaying strong mixing coefficients, $\alpha(n) \le c\,a^n$ for some $0 \le a < 1$, and with $E[Y_0^2\log^+|Y_0|] < \infty$. Assume moreover that the normalized variances converge,
--   $$
--   \frac{1}{n} \mathrm{Var}(S_n) \to \sigma^2, \qquad S_n = \sum_{i=0}^{n-1} Y_i,
--   $$
--   where $\sigma^2 = E[Y_0^2] + 2\sum_{k \ge 1} E[Y_0 Y_k]$, and that $\sigma^2 > 0$. Then
--   $$
--   \frac{1}{\sqrt n} S_n \xrightarrow{d} N(0, \sigma^2).
--   $$
--   This is the blocking half of the Doukhan-Massart-Rio central limit theorem (Jones, Theorem 6): Bernstein big-block/small-block decomposition makes distant blocks asymptotically independent at an exponential rate, so the normalized sum inherits the Gaussian limit from the independent-block approximation once the variance is known to stabilize. It takes the variance limit as a hypothesis, complementing the separately proved variance-convergence lemma.
--   **Formalization Note** Convergence is weak convergence of the laws under the common probability measure $P$; the Gaussian variance is the nonnegative-real coercion of $\sigma^2$, which equals $\sigma^2$ under the positivity hypothesis.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 6 and eq. Doukhan-Massart-Rio; original result: P. Doukhan, P. Massart and E. Rio (1994). Blocking step of the proof.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- The blocking/limit component of the Doukhan-Massart-Rio CLT, given variance convergence. -/

theorem MarkovChainCLT.clt_of_var_limit_of_exp_alpha
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by sorry
