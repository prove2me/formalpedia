-- Prove2me | Theorems.Thm_levy_foundations_poissonTimeCountLaw
-- name    : levy_foundations_poissonTimeCountLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:18:30.788704+00:00
-- url     : https://prove2.me/theorems/4939d434-0c5a-4828-b028-d97cc75ba46e
-- title:
--   Poisson law of the running time-space point count
-- statement:
--   The count on (0,t] × A follows a Poisson law of parameter t m(A) for nonnegative t and a measurable mark set of finite intensity.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L125-L133. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonTimeCount

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_poissonTimeCountLaw
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × E) (A : Set E) (t : ℝ)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod m) μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (LevyFoundations.poissonTimeCount K X A t) =
      (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map
        (Nat.cast : ℕ → ℝ≥0∞) := by sorry
