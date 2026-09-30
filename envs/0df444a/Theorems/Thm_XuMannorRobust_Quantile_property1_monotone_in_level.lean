-- Prove2me | Theorems.Thm_XuMannorRobust_Quantile_property1_monotone_in_level
-- name    : XuMannorRobust.Quantile.property1_monotone_in_level
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T16:11:12.378527+00:00
-- url     : https://prove2.me/theorems/b4b4de49-c8e9-4a77-b4f8-6e9618a34b67
-- title:
--   Appendix C, property 1 — $\mathbb Q^\beta$ and $\mathbb T^\beta$ are nondecreasing in $\beta$
-- statement:
--   Let $X$ be a nonnegative random variable whose law $P$ is a probability measure on $\mathbb R$ with $P((-\infty, 0)) = 0$. If $0 \le \beta_2 \le \beta_1 \le 1$, where $\beta_1 = 1$ is allowed only when $X$ is bounded above ($P((-\infty, M]) = 1$ for some $M$), then
--
--   $$\mathbb Q^{\beta_1}(X) \ge \mathbb Q^{\beta_2}(X), \qquad \mathbb T^{\beta_1}(X) \ge \mathbb T^{\beta_2}(X),$$
--
--   where $\mathbb Q^\beta$ is the $\beta$-quantile value and $\mathbb T^\beta$ the $\beta$-truncated mean (Definition 3, corrected second branch).
--
--   This monotonicity lets the proof of Theorem 5 move between the confidence-shifted levels $\beta \pm \lambda_0 \pm (n - \hat n)/n$.
--
--   **Formalization Note** The paper states the property for $X$ supported on $\mathbb R^+$ and arbitrary $\beta_1 \ge \beta_2$. The levels are restricted to $[0, 1]$, and the top level $\beta_1 = 1$ to variables bounded above. At those excluded levels the paper's values are $+\infty$ ($\mathbb Q^1(X)$ for unbounded $X$; the empty defining set for $\beta > 1$), where the inequality holds trivially in the extended reals. Lean's real $\inf \emptyset = 0$ would falsify it there. No case with finite values is excluded.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 415, Appendix C (Proof of Theorem 5), property 1

import Mathlib
import Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean

open MeasureTheory

namespace XuMannorRobust.Quantile

/-- **Appendix C, property 1** (Xu & Mannor 2012, p. 415). Let `X` be a random variable with law
`P`, supported on `ℝ⁺` (`P((-∞, 0)) = 0`). If `0 ≤ β₂ ≤ β₁ ≤ 1`, then `ℚ^{β₁}(X) ≥ ℚ^{β₂}(X)` and
`𝕋^{β₁}(X) ≥ 𝕋^{β₂}(X)`. The top level `β₁ = 1` is allowed only when `X` is bounded above
(`P((-∞, M]) = 1` for some `M`): for unbounded `X` the paper's `ℚ¹(X)` is `+∞`, which Lean's real
`sInf ∅ = 0` cannot represent. -/
theorem property1_monotone_in_level (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Set.Iio 0) = 0) (β₁ β₂ : ℝ) (hβ₂ : 0 ≤ β₂) (h21 : β₂ ≤ β₁) (hβ₁ : β₁ ≤ 1)
    (hfin : β₁ < 1 ∨ ∃ M : ℝ, P (Set.Iic M) = 1) :
    quantileValue P β₂ ≤ quantileValue P β₁ ∧ truncatedMean P β₂ ≤ truncatedMean P β₁ := by sorry

end XuMannorRobust.Quantile
