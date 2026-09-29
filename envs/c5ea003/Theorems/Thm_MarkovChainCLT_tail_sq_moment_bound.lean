-- Prove2me | Theorems.Thm_MarkovChainCLT_tail_sq_moment_bound
-- name    : MarkovChainCLT.tail_sq_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-05T01:01:58.098525+00:00
-- url     : https://prove2.me/theorems/a70423b8-2f3b-4c08-b9ca-8d40bd8703b9
-- title:
--   Tail second moment via $(2+\delta)$-moment
-- statement:
--   Truncated tail second moments from higher moments.
--
--   Let $Y$ be measurable with $E|Y|^{2+\delta}<\infty$ ($\delta>0$) and $M>0$. Then
--
--   $$
--   E[Y^2\mathbf 1_{\{|Y|>M\}}]\le\frac{E|Y|^{2+\delta}}{M^\delta}.
--   $$
--
--   Pointwise on $\{|Y|>M\}$ this is $|Y|^2=|Y|^{2+\delta}/|Y|^\delta\le|Y|^{2+\delta}/M^\delta$; off the set both sides vanish. Integration preserves it.
--
--   **Formalization Note** Real powers; indicators are `Set.indicator` of constant $1$.
-- source:
--   Markov/Chebyshev tail estimate for Davydov truncation

import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem MarkovChainCLT.tail_sq_moment_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (δ M : ℝ) (hδ : 0 < δ) (hM : 0 < M) (hYm : Measurable Y) (hmom : Integrable (fun ω => |Y ω| ^ (2 + δ)) P) : ∫ ω, (Y ω) ^ 2 * Set.indicator {ω | M < |Y ω|} 1 ω ∂P ≤ (∫ ω, |Y ω| ^ (2 + δ) ∂P) / M ^ δ := by sorry
