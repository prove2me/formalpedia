-- Prove2me | Theorems.Thm_variance_partialIntegral_le_integral_variance
-- name    : variance_partialIntegral_le_integral_variance
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T15:25:54.717655+00:00
-- url     : https://prove2.me/theorems/660b4bae-f293-422c-80e3-53077f5bbb52
-- statement:
--   Let $\rho$ and $\sigma$ be probability measures on measurable spaces $\beta$ and $\gamma$, and let $W \in L^2(\rho \otimes \sigma)$ be square-integrable on the product. Write the $\rho$-partial average $g(y) = \int W(x,y)\, d\rho(x)$. Then the $\sigma$-variance of the partial average is bounded by the $\rho$-average of the fiberwise $\sigma$-variances:
--
--   $$\operatorname{Var}_{y\sim\sigma}\!\Big(\int W(x,y)\,d\rho(x)\Big) \;\le\; \int \operatorname{Var}_{y\sim\sigma}\big(W(x,\cdot)\big)\, d\rho(x).$$
--
--   This is the convexity-of-variance / conditional-Jensen (ANOVA) inequality $\operatorname{Var}(\mathbb{E}[\,\cdot\,|\mathcal{G}]) \le \mathbb{E}[\operatorname{Var}(\,\cdot\,|\mathcal{G})]$ read for a product measure, where conditioning on the second factor is the partial integral over the first. It is the per-step Jensen estimate $\mathbb{E}[\Delta_k^2] \le \mathbb{E}[\operatorname{Var}_k f]$ that drives the Efron–Stein tensorization of variance. The proof centers $W$ by subtracting its first-factor partial integral and applies the conditional Jensen inequality for the convex map $t \mapsto t^2$ to the conditional expectation given the second factor. Source: R. van Handel, *Probability in High Dimension* (APC 550), §2.1 (proof of Thm 2.3); Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Ch. 3.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550), §2.1 (proof of Theorem 2.3, the per-step Jensen estimate E[Δ_k²] ≤ E[Var_k]); Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem variance_partialIntegral_le_integral_variance
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    variance (fun y => ∫ x, W (x, y) ∂ρ) σ
      ≤ ∫ x, variance (fun y => W (x, y)) σ ∂ρ := by sorry
