-- Prove2me | Theorems.Thm_levy_foundations_compoundDriverArrivalStrictMono
-- name    : levy_foundations_compoundDriverArrivalStrictMono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:44:54.744877+00:00
-- url     : https://prove2.me/theorems/54be42f8-539c-4d45-ab14-b6baf2123b3c
-- title:
--   Arrival times are almost surely strictly increasing
-- statement:
--   Arrival times are almost surely strictly increasing.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L147

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem levy_foundations_compoundDriverArrivalStrictMono
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, StrictMono (fun n => LevyFoundations.arrival τ n ω) := by sorry
