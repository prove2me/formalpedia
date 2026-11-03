-- Prove2me | Theorems.Thm_levy_foundations_finiteDimDistributionRestrict
-- name    : levy_foundations_finiteDimDistributionRestrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:16:58.760653+00:00
-- url     : https://prove2.me/theorems/d26de7d2-ad68-41e0-9119-0ad480fd83b9
-- title:
--   Restricting a finite-dimensional law recovers the smaller joint law
-- statement:
--   Restricting a finite-dimensional law recovers the smaller joint law.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/FiniteDimensional.lean#L72

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_finiteDimMap
import Definitions.Def_levy_foundations_finiteDimDistribution

open MeasureTheory
open scoped NNReal

theorem levy_foundations_finiteDimDistributionRestrict
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (hX : ∀ t, Measurable (X t))
    {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (LevyFoundations.finiteDimDistribution X μ I).map
      (Finset.restrict₂ (π := fun _ => E) hJI) =
      LevyFoundations.finiteDimDistribution X μ J := by sorry
