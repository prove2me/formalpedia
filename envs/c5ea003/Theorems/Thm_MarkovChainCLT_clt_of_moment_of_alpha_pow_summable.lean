-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_moment_of_alpha_pow_summable
-- name    : MarkovChainCLT.clt_of_moment_of_alpha_pow_summable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:39:50.502507+00:00
-- url     : https://prove2.me/theorems/d340a9f0-ad5a-41b7-82ad-0bd52a349527
-- title:
--   Ibragimov–Linnik CLT, moment case: $E|Y|^{2+\delta} < \infty$, $\sum \alpha(n)^{\delta/(2+\delta)} < \infty$ (Jones Thm 5(ii))
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$. Suppose there is $\delta > 0$ with $E|Y_0|^{2+\delta} < \infty$ and
--
--   $$
--   \sum_{n} \alpha(n)^{\delta/(2+\delta)} \;<\; \infty.
--   $$
--
--   Then the series
--
--   $$
--   \sigma^2 \;=\; E[Y_0^2] \;+\; 2 \sum_{k \ge 1} E[Y_0 Y_k]
--   $$
--
--   converges absolutely, and if $\sigma^2 > 0$ then $S_n / \sqrt{n} \xrightarrow{d} N(0, \sigma^2)$ as $n \to \infty$.
--
--   This is the moment case of the Ibragimov–Linnik central limit theorem (the source's eq. (10)), the engine behind the Chan–Geyer and polynomial-moment chain CLTs.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 5, condition 2, eq. (10) (arXiv v2 p. 9); originals: I. A. Ibragimov (1962); Ibragimov & Linnik (1971), Theorem 18.5.3

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 5, condition 2** (Ibragimov 1962; Ibragimov–Linnik 1971): a centered
strictly stationary strongly mixing sequence with `E|Y₀|^{2+δ} < ∞` and
`∑_n α(n)^{δ/(2+δ)} < ∞` satisfies `σ² = E[Y₀²] + 2 ∑_{k≥1} E[Y₀ Y_k]`
(absolutely convergent), and if `σ² > 0` then `S_n / √n →d N(0, σ²)`. -/

theorem MarkovChainCLT.clt_of_moment_of_alpha_pow_summable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ) (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P)
    (hα : Summable (fun n => alphaMixingCoef P Y n ^ (δ / (2 + δ)))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by sorry
