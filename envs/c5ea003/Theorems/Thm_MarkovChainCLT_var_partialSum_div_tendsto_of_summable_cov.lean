-- Prove2me | Theorems.Thm_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov
-- name    : MarkovChainCLT.var_partialSum_div_tendsto_of_summable_cov
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T06:43:33.437819+00:00
-- url     : https://prove2.me/theorems/1d16d210-7e2c-49f0-8c1e-81d6ab064449
-- title:
--   Variance convergence for partial sums under summable autocovariances
-- statement:
--   Let $Y = (Y_n)_{n \ge 0}$ be a centered strictly stationary real-valued sequence on a probability space $(\Omega, \mathcal F, P)$ with $Y_0 \in L^2$, and assume its positive-lag autocovariances are absolutely summable, $\sum_{k \ge 1} |E[Y_0 Y_k]| < \infty$. Write $S_n = \sum_{i=0}^{n-1} Y_i$ and
--   $$
--   \sigma^2 = E[Y_0^2] + 2\sum_{k \ge 1} E[Y_0 Y_k].
--   $$
--   Then the normalized variances converge,
--   $$
--   \frac{1}{n} \mathrm{Var}(S_n) \to \sigma^2 \qquad (n \to \infty).
--   $$
--   This is the variance half of the summable-$\rho$ central limit theorem (Jones, Theorem 7; Ibragimov 1975): stationarity turns $\mathrm{Var}(S_n)$ into $n c_0 + 2\sum_{k=1}^{n-1}(n-k)c_k$ with $c_k = E[Y_0 Y_k]$, and absolute summability makes the Cesaro-weighted correction vanish. It separates the second-moment computation from the blocking argument that upgrades variance convergence to convergence in distribution.
--
--   **Formalization Note** Lean states the limit with `Filter.Tendsto` toward `nhds` of `seqAsymptoticVariance P Y`, the platform's $E[Y_0^2] + 2\sum'$ definition; the series is the honest limit under the summability hypothesis.
-- source:
--   G. L. Jones, On the Markov Chain Central Limit Theorem, Probability Surveys 1 (2004) 299-320, https://arxiv.org/abs/math/0409112, Theorem 7 and eq. (12); original result: I. A. Ibragimov, Theory of Probability and Its Applications 20 (1975). Variance-convergence step of the proof.

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- The variance-convergence component of the summable-rho CLT. -/

theorem MarkovChainCLT.var_partialSum_div_tendsto_of_summable_cov
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)) :
    Tendsto (fun n : ℕ => Var[∑ i ∈ Finset.range n, Y i; P] / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)) := by sorry
