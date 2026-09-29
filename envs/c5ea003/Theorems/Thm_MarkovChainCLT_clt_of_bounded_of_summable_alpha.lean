-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_summable_alpha
-- name    : MarkovChainCLT.clt_of_bounded_of_summable_alpha
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:39:31.817381+00:00
-- url     : https://prove2.me/theorems/28e11174-83a0-4458-9c87-f4c802fea390
-- title:
--   Ibragimov–Linnik CLT, bounded case: $|Y| < B$ a.s., $\sum \alpha(n) < \infty$ (Jones Thm 5(i))
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$. Suppose there is a constant $B$ with $|Y_n| < B$ almost surely for every $n$, and the strong mixing coefficients are summable, $\sum_n \alpha(n) < \infty$.
--
--   Then the series
--
--   $$
--   \sigma^2 \;=\; E[Y_0^2] \;+\; 2 \sum_{k \ge 1} E[Y_0 Y_k]
--   $$
--
--   converges absolutely, and if $\sigma^2 > 0$ then $S_n / \sqrt{n} \xrightarrow{d} N(0, \sigma^2)$ as $n \to \infty$.
--
--   This is the bounded case of the Ibragimov–Linnik central limit theorem, the engine behind the polynomial-ergodicity CLT for bounded functionals (goal condition 1) — the regime of posterior probabilities in Bayesian MCMC.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 5, condition 1 (arXiv v2 p. 9); originals: I. A. Ibragimov (1962); Ibragimov & Linnik (1971), Ch. 18

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 5, condition 1** (Ibragimov 1962; Ibragimov–Linnik 1971): a centered
strictly stationary strongly mixing sequence that is uniformly bounded and has
summable strong mixing coefficients satisfies
`σ² = E[Y₀²] + 2 ∑_{k≥1} E[Y₀ Y_k]` (absolutely convergent), and if `σ² > 0` then
`S_n / √n →d N(0, σ²)`. -/

theorem MarkovChainCLT.clt_of_bounded_of_summable_alpha {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by sorry
