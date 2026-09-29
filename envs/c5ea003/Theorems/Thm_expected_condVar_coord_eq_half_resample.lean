-- Prove2me | Theorems.Thm_expected_condVar_coord_eq_half_resample
-- name    : expected_condVar_coord_eq_half_resample
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T06:20:14.355486+00:00
-- url     : https://prove2.me/theorems/a5e692e2-aa33-4da7-97d2-d1f913a1b51c
-- statement:
--   Let $\mu_i$ be probability measures on measurable spaces $\alpha_i$ over a finite index type $\iota$, and let $Z$ be square-integrable on the product cube with the independent-coordinate measure $\bigotimes_i \mu_i$ (`Measure.pi μ`). For a fixed coordinate $i$, the per-coordinate conditional variance is $\operatorname{Var}_i Z(\omega) = \operatorname{Var}_{x\sim\mu_i}\, Z(\omega \text{ with } i\text{-th coordinate replaced by } x)$ (`variance (fun x => Z (Function.update ω i x)) (μ i)`). Then its expectation over $\omega \sim \bigotimes_j \mu_j$ equals half the expected squared single-coordinate resampling difference on the doubled product cube:
--
--   $$\int \operatorname{Var}_i Z(\omega)\, d\!\bigotimes_j\mu_j(\omega) \;=\; \tfrac12 \int\!\!\int \big(Z(\omega) - Z(\omega \text{ with } i\text{-th coord} = \omega'_i)\big)^2 \, d\big(\bigotimes\mu \otimes \bigotimes\mu\big)(\omega,\omega').$$
--
--   This is the per-coordinate global resampling identity at the heart of the factor $\tfrac12$ in the Efron–Stein inequality: it identifies the expected conditional variance contributed by coordinate $i$ with the expected square of the difference produced by independently resampling that single coordinate. Combined over all coordinates with the variance tensorization spine it yields $\operatorname{Var}(Z) \le \tfrac12 \sum_i \mathbb{E}\,(Z - Z'_i)^2$. The proof applies the single-measure symmetrization $\operatorname{Var}(W)=\tfrac12\mathbb{E}(W-W')^2$ fiberwise in coordinate $i$, then collapses the resulting double integral via the measure-preservation of the single-coordinate resample map and Fubini. Source: R. van Handel, *Probability in High Dimension* (APC 550), §2.1; Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Ch. 3, Thm 3.1.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550), §2.1; Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3, Theorem 3.1 (Efron–Stein resampling form).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

theorem expected_condVar_coord_eq_half_resample
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) {Z : (∀ j, α j) → ℝ} (hZ : MemLp Z 2 (Measure.pi μ)) :
    (∫ ω, variance (fun x => Z (Function.update ω i x)) (μ i) ∂(Measure.pi μ))
      = (∫ p, (Z p.1 - Z (Function.update p.1 i (p.2 i))) ^ 2
          ∂((Measure.pi μ).prod (Measure.pi μ))) / 2 := by sorry
