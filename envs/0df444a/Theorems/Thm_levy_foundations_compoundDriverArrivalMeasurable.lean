-- Prove2me | Theorems.Thm_levy_foundations_compoundDriverArrivalMeasurable
-- name    : levy_foundations_compoundDriverArrivalMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:43:40.762806+00:00
-- url     : https://prove2.me/theorems/0f39a1d2-c45c-4a2e-845c-e3e8eeda8fca
-- title:
--   Arrival times are measurable functions of the driver
-- statement:
--   Arrival times are measurable functions of the driver.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L108

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem levy_foundations_compoundDriverArrivalMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (n : ℕ) :
    Measurable (LevyFoundations.arrival τ n) := by sorry
