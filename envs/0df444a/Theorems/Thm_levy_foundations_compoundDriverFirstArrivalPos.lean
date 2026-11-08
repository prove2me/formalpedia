-- Prove2me | Theorems.Thm_levy_foundations_compoundDriverFirstArrivalPos
-- name    : levy_foundations_compoundDriverFirstArrivalPos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:48:06.690338+00:00
-- url     : https://prove2.me/theorems/744a969e-3cf6-4d77-9803-b29687228d30
-- title:
--   First compound-Poisson arrival is almost surely positive
-- statement:
--   First compound-Poisson arrival is almost surely positive.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L161

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

theorem levy_foundations_compoundDriverFirstArrivalPos
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω} (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) : ∀ᵐ ω ∂μ, 0 < LevyFoundations.arrival τ 0 ω := by sorry
