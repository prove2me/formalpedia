-- Prove2me | Theorems.Thm_levy_foundations_compensatedPoissonSumIsometry
-- name    : levy_foundations_compensatedPoissonSumIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T15:18:13.973236+00:00
-- url     : https://prove2.me/theorems/ce8c76b2-edba-4b5e-9bda-51c3b0a0e3e7
-- title:
--   Compensated Poisson L2 isometry for L1 ∩ L2 integrands
-- statement:
--   Campbell's second formula: the second moment of the compensated Poisson series equals the L2 mass of its integrand, assuming L1 ∩ L2.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean#L379-L386. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_compensatedPoissonSum

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_compensatedPoissonSumIsometry
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, (LevyFoundations.compensatedPoissonSum m K X f ω) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂m := by sorry
