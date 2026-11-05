-- Prove2me | Theorems.Thm_levy_foundations_compoundDriverArrivalDiverges
-- name    : levy_foundations_compoundDriverArrivalDiverges
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:45:18.142328+00:00
-- url     : https://prove2.me/theorems/9a47a925-ae84-4e29-8b77-5f31e660dedb
-- title:
--   Compound-Poisson arrival times almost surely diverge to infinity
-- statement:
--   Compound-Poisson arrival times almost surely diverge to infinity.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L190

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem levy_foundations_compoundDriverArrivalDiverges
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => LevyFoundations.arrival τ n ω) atTop atTop := by sorry
