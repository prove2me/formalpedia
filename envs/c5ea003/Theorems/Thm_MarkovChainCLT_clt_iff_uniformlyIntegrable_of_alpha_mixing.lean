-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing
-- name    : MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:38:53.944463+00:00
-- url     : https://prove2.me/theorems/58818f96-6c6c-41e1-9d51-78918e104355
-- title:
--   Strongly mixing stationary sequences: CLT $\iff$ $\{S_n^2/\sigma_n^2\}$ uniformly integrable (Jones Thm 3)
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$ and $\sigma_n^2 = E[S_n^2]$. Suppose $E[Y_0^2] < \infty$, the sequence is strongly mixing ($\alpha(n) \to 0$), and $\sigma_n^2 \to \infty$. Then the following are equivalent:
--
--   $$
--   \frac{S_n}{\sigma_n} \xrightarrow{d} N(0, 1) \qquad \Longleftrightarrow \qquad \Bigl\{ \frac{S_n^2}{\sigma_n^2} : n \ge 1 \Bigr\} \text{ is uniformly integrable.}
--   $$
--
--   This characterization (Cogburn; Denker; Mori–Yoshihara) explains exactly what can fail for dependent sequences with second moments: the CLT is equivalent to uniform integrability of the normalized squares, not implied by moments alone.
--
--   **Formalization Note** For the (finitely many) indices with $\sigma_n = 0$ the normalized quantities are interpreted as $0$. Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 3 (arXiv v2 p. 9); originals: R. Cogburn (1960), M. Denker (1986), T. Mori & K. Yoshihara (1986)

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 3** (Cogburn 1960; Denker 1986; Mori–Yoshihara 1986): for a centered
strictly stationary strongly mixing square-integrable sequence with
`σ_n² = E[S_n²] → ∞`, the normalized sums `S_n / σ_n` converge in distribution to
`N(0,1)` **iff** the family `{S_n² / σ_n²}` is uniformly integrable. -/

theorem MarkovChainCLT.clt_iff_uniformlyIntegrable_of_alpha_mixing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hmix : Tendsto (fun n => alphaMixingCoef P Y n) atTop (𝓝 0))
    (hvar : Tendsto (fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) atTop atTop) :
    TendstoInDistribution
        (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω)
          / Real.sqrt (∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P))
        atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1)
      ↔ UniformIntegrable
          (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
            / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by sorry
