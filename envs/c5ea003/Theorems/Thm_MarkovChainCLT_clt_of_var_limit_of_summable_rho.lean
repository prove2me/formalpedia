-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_var_limit_of_summable_rho
-- name    : MarkovChainCLT.clt_of_var_limit_of_summable_rho
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T06:51:28.547998+00:00
-- url     : https://prove2.me/theorems/d190243f-e343-490f-bd79-f997e0843ec9
-- title:
--   CLT for summable-$\rho$ sequences given variance convergence
-- statement:
--   Let $Y = (Y_n)_{n \ge 0}$ be a centered strictly stationary real-valued sequence on a probability space $(\Omega, \mathcal F, P)$ with $Y_0 \in L^2$ and summable maximal-correlation coefficients, $\sum_n \rho(n) < \infty$. Assume moreover that the normalized variances converge,
--   $$
--   \frac{1}{n} \mathrm{Var}(S_n) \to \sigma^2, \qquad S_n = \sum_{i=0}^{n-1} Y_i,
--   $$
--   where $\sigma^2 = E[Y_0^2] + 2\sum_{k \ge 1} E[Y_0 Y_k]$, and that $\sigma^2 > 0$. Then
--   $$
--   \frac{1}{\sqrt n} S_n \xrightarrow{d} N(0, \sigma^2).
--   $$
--   This is the blocking half of the summable-$\rho$ central limit theorem (Jones, Theorem 7; Ibragimov 1975): Bernstein big-block/small-block decomposition makes distant blocks asymptotically independent (quantified by $\rho$), so the normalized sum inherits the Gaussian limit from the independent-block approximation once the variance is known to stabilize. It takes the variance limit as a hypothesis, complementing the separately proved variance-convergence lemma.
--
--   **Formalization Note** Convergence is weak convergence of the laws under the common probability measure $P$; the Gaussian variance is the nonnegative-real coercion of $\sigma^2$, which equals $\sigma^2$ under the positivity hypothesis.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 7 and eq. (12); original result: I. A. Ibragimov, Theory of Probability and Its Applications 20 (1975). Blocking step of the proof.

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- The blocking/limit component of the summable-rho CLT, given variance convergence. -/

theorem MarkovChainCLT.clt_of_var_limit_of_summable_rho
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hρ : Summable (fun n => rhoMixingCoef P Y n))
    (hvarlim : Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
      atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal) := by sorry
