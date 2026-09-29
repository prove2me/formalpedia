-- Prove2me | Theorems.Thm_hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
-- name    : hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:45:00.264345+00:00
-- url     : https://prove2.me/theorems/45e99ff3-362b-4dba-b587-8523ea5010f7
-- title:
--   Conditional Hoeffding lemma: bounded and conditionally centred is sub-Gaussian
-- statement:
--   Conditional Hoeffding lemma. Let $X$ be a measurable random variable on a standard Borel probability space that is almost surely in $[a,b]$ and has conditional expectation zero given a sub-sigma-algebra $m$ ($\mu[X\mid m]=0$ a.e.). Then $X$ is conditionally sub-Gaussian over the conditional-expectation kernel $\mathrm{condExpKernel}\,\mu\,m$ with parameter $((b-a)/2)^2$. This is the fiberwise (kernel) analog of the measure-level Hoeffding lemma hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero, and is the bridge that turns a bounded, conditionally-centered martingale difference into the HasCondSubgaussianMGF hypothesis consumed by the Azuma-Hoeffding inequality (the engine of McDiarmid bounded-differences).
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities (Oxford 2013), Sec 2.6 (Hoeffding lemma) and Sec 6.1 (martingale/bounded-differences method); Hoeffding, JASA 58 (1963) Sec 2. Conditional version = fiberwise Hoeffding over the regular conditional distribution (condExpKernel), a Markov kernel.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {X : Ω → ℝ} {a b : ℝ}
    (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by sorry
