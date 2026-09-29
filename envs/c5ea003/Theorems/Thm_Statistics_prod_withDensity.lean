-- Prove2me | Theorems.Thm_Statistics_prod_withDensity
-- name    : Statistics.prod_withDensity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:12.062289+00:00
-- url     : https://prove2.me/theorems/79a40fe9-b4c4-43ec-a259-2c80f024860e
-- title:
--   A product of tilted measures is the product tilted by the product density
-- statement:
--   **A product of tilted measures is the product tilted by the product density.** Let $\eta_1, \eta_2$ be $\sigma$-finite measures and $f_1, f_2$ measurable densities with values in $[0,\infty]$, such that the tilted measures $\eta_i \cdot f_i$ are again $\sigma$-finite. Then
--   $$(\eta_1 \otimes \eta_2)\cdot\bigl((x,y) \mapsto f_1(x) f_2(y)\bigr) \;=\; (\eta_1 \cdot f_1) \otimes (\eta_2 \cdot f_2),$$
--   where $\mu \cdot f$ denotes $\mathrm{withDensity}$, the measure $A \mapsto \int_A f \,\mathrm{d}\mu$. Equivalently: if $\nu_i \ll \eta_i$ with densities $f_i$, then $\nu_1 \otimes \nu_2 \ll \eta_1 \otimes \eta_2$ with density $f_1 \otimes f_2$. The proof only has to check the identity on measurable rectangles, where it is the product rule for the lower integral.
-- source:
--   Standard; see O. Kallenberg, Foundations of Modern Probability, 3rd ed., Springer, 2021, Chapter 1 (Theorem 1.29, Fubini-Tonelli) together with the Radon-Nikodym theorem (Theorem 2.10); the statement is the product form of the chain rule for densities.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.prod_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (η₁ : Measure α) (η₂ : Measure β) [SigmaFinite η₁] [SigmaFinite η₂]
    {f₁ : α → ℝ≥0∞} {f₂ : β → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    [SigmaFinite (η₁.withDensity f₁)] [SigmaFinite (η₂.withDensity f₂)] :
    (η₁.prod η₂).withDensity (fun z => f₁ z.1 * f₂ z.2)
      = (η₁.withDensity f₁).prod (η₂.withDensity f₂) := by sorry
