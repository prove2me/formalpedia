-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_exp_alpha_of_log_moment
-- name    : MarkovChainCLT.clt_of_exp_alpha_of_log_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:40:46.941933+00:00
-- url     : https://prove2.me/theorems/46f1ee32-56c3-43ee-8783-875e4c0b3a6a
-- title:
--   Doukhan–Massart–Rio CLT: $\alpha(n) = O(a^n)$, $E[Y^2\log^+|Y|] < \infty$ (Jones Thm 6)
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$. Suppose the strong mixing coefficients decay exponentially, $\alpha(n) \le c\, a^n$ for some $0 \le a < 1$, and
--
--   $$
--   E\bigl[Y_0^2 \, \log^+ |Y_0|\bigr] < \infty, \qquad \log^+ t = \max(0, \log t).
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
--   This Doukhan–Massart–Rio theorem trades the $2+\delta$ moment for a barely-more-than-second moment when mixing is exponentially fast — the sharpest sequence-level input available for geometrically ergodic chains.
--
--   **Formalization Note** The stated moment already implies $E[Y_0^2] < \infty$, so square-integrability is not assumed separately. Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 6 (arXiv v2 p. 11); original: P. Doukhan, P. Massart & E. Rio, Ann. Inst. H. Poincare Probab. Statist. 30 (1994) (special case)

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 6** (Doukhan–Massart–Rio 1994): a centered strictly stationary
sequence with exponentially fast strong mixing and `E[Y₀² log⁺|Y₀|] < ∞` satisfies
`σ² = E[Y₀²] + 2 ∑_{k≥1} E[Y₀ Y_k]` (absolutely convergent), and if `σ² > 0` then
`S_n / √n →d N(0, σ²)`. -/

theorem MarkovChainCLT.clt_of_exp_alpha_of_log_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by sorry
