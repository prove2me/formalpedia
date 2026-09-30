-- Prove2me | Theorems.Thm_XuMannorRobust_Quantile_property2_stochastic_dominance
-- name    : XuMannorRobust.Quantile.property2_stochastic_dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T16:13:27.250415+00:00
-- url     : https://prove2.me/theorems/8cedd0b2-d20d-456f-9a97-25f9993b3819
-- title:
--   Appendix C, property 2 — $\mathbb Q^\beta$ and $\mathbb T^\beta$ are monotone under stochastic dominance
-- statement:
--   Let $X$ and $Y$ be nonnegative random variables with laws $P$ and $P'$, probability measures on $\mathbb R$ with $P((-\infty,0)) = P'((-\infty,0)) = 0$. Suppose $Y$ stochastically dominates $X$:
--
--   $$\Pr(Y \ge a) \ge \Pr(X \ge a) \quad \text{for all } a \in \mathbb R.$$
--
--   Then for every level $\beta \in [0, 1]$, where $\beta = 1$ is allowed only when $Y$ is bounded above ($P'((-\infty, M]) = 1$ for some $M$),
--
--   $$\mathbb Q^{\beta}(Y) \ge \mathbb Q^{\beta}(X), \qquad \mathbb T^{\beta}(Y) \ge \mathbb T^{\beta}(X),$$
--
--   with $\mathbb Q^\beta$ the $\beta$-quantile value and $\mathbb T^\beta$ the $\beta$-truncated mean (Definition 3, corrected second branch).
--
--   In the proof of Theorem 5 this is what compares the sample distribution with the discrete distributions supported on the cell minimizers.
--
--   **Formalization Note** The paper says "for any $\beta$"; the levels are restricted to $[0, 1]$, where Definition 3 is meaningful, and both variables are taken nonnegative (Definition 3's standing assumption). The level $\beta = 1$ additionally requires $Y$ to be bounded above. For unbounded $Y$ the paper's $\mathbb Q^1(Y)$ is $+\infty$ and the inequality is trivial, but Lean's junk value $\inf\emptyset = 0$ would falsify it.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 415, Appendix C (Proof of Theorem 5), property 2

import Mathlib
import Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean

open MeasureTheory

namespace XuMannorRobust.Quantile

/-- **Appendix C, property 2** (Xu & Mannor 2012, p. 415). Let `X` and `Y` be nonnegative random
variables with laws `P` and `P'` (`P((-∞, 0)) = P'((-∞, 0)) = 0`). If `Y` stochastically dominates
`X`, i.e. `Pr(Y ≥ a) ≥ Pr(X ≥ a)` for all `a ∈ ℝ`, then for every level `β ∈ [0, 1]`,
`ℚ^β(Y) ≥ ℚ^β(X)` and `𝕋^β(Y) ≥ 𝕋^β(X)`. The level `β = 1` is allowed only when `Y` is bounded
above (`P'((-∞, M]) = 1` for some `M`): for unbounded `Y` the paper's `ℚ¹(Y)` is `+∞`, which
Lean's real `sInf ∅ = 0` cannot represent. -/
theorem property2_stochastic_dominance (P P' : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (hP : P (Set.Iio 0) = 0) (hP' : P' (Set.Iio 0) = 0)
    (hdom : ∀ a : ℝ, P (Set.Ici a) ≤ P' (Set.Ici a)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P' (Set.Iic M) = 1) :
    quantileValue P β ≤ quantileValue P' β ∧ truncatedMean P β ≤ truncatedMean P' β := by sorry

end XuMannorRobust.Quantile
