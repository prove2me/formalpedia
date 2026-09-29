-- Prove2me | Theorems.Thm_variance_partial_integral_le
-- name    : variance_partial_integral_le
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T07:07:58.078073+00:00
-- url     : https://prove2.me/theorems/5242932f-faaa-4cc5-b203-3a52e34b2d13
-- statement:
--   Let $\rho$ and $\sigma$ be probability measures on measurable spaces $\beta$ and $\gamma$, and let $W \in L^2(\rho \otimes \sigma)$. Form the partial average over the first factor, $g(c) = \int_\beta W(x,c)\, d\rho(x)$ (`fun c => ∫ x, W (x, c) ∂ρ`). Then the variance of $g$ under $\sigma$ is at most the full variance of $W$ under the product measure:
--
--   $$\operatorname{Var}_\sigma\!\Big(c \mapsto \int_\beta W(x,c)\, d\rho(x)\Big) \;\le\; \operatorname{Var}_{\rho\otimes\sigma}(W).$$
--
--   This is the conditional-Jensen variance contraction $\operatorname{Var}\big(\mathbb{E}[W\mid \sigma(\mathrm{snd})]\big) \le \operatorname{Var}(W)$: averaging out one independent block of coordinates can only decrease the variance. The key step identifies the conditional expectation $\mathbb{E}[W \mid \sigma(\mathrm{snd})]$ with the partial integral $g$ over the first factor, after which the law of total variance $\mathbb{E}\,\operatorname{Var}(W\mid\mathcal G) + \operatorname{Var}(\mathbb{E}[W\mid\mathcal G]) = \operatorname{Var}(W)$ gives the inequality by dropping the nonnegative $\mathbb{E}\,\operatorname{Var}(W\mid\mathcal G)$ term, and a measure-preservation argument drops the redundant first factor. This is precisely the per-step Jensen contraction ($\mathbb{E}[\Delta_k^2] \le \mathbb{E}[\operatorname{Var}_k]$) in the Doob-martingale proof of the Efron–Stein tensorization of variance. The conditional-expectation-as-partial-integral identification is the two-factor brick `efron_stein_condExp_comap_snd_eq_partial_integral` (inlined here for a self-contained proof). Source: R. van Handel, *Probability in High Dimension* (APC 550), §2.1; Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Ch. 3.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550), §2.1; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3 (Efron–Stein; conditional-Jensen variance contraction).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem variance_partial_integral_le {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    variance (fun c => ∫ x, W (x, c) ∂ρ) σ ≤ variance W (ρ.prod σ) := by sorry
