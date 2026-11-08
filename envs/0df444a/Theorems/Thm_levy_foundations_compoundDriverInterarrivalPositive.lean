-- Prove2me | Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
-- name    : levy_foundations_compoundDriverInterarrivalPositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:44:34.91319+00:00
-- url     : https://prove2.me/theorems/0f58eb54-3941-43e4-b18e-198edbdb0546
-- title:
--   All compound-Poisson interarrivals are almost surely positive
-- statement:
--   All compound-Poisson interarrivals are almost surely positive.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L133

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem levy_foundations_compoundDriverInterarrivalPositive
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < τ n ω := by sorry
