-- Prove2me | Theorems.Thm_levy_foundations_finiteDimDistributionProjective
-- name    : levy_foundations_finiteDimDistributionProjective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:17:13.358015+00:00
-- url     : https://prove2.me/theorems/22ccb666-6f48-4a03-b7c7-3eb99b04671c
-- title:
--   Finite-dimensional distributions form a consistent projective measure family
-- statement:
--   Finite-dimensional distributions form a consistent projective measure family.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/FiniteDimensional.lean#L89

import Mathlib.MeasureTheory.Constructions.Projective
import Definitions.Def_levy_foundations_finiteDimMap
import Definitions.Def_levy_foundations_finiteDimDistribution

open MeasureTheory
open scoped NNReal

theorem levy_foundations_finiteDimDistributionProjective
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (hX : ∀ t, Measurable (X t)) :
    IsProjectiveMeasureFamily (α := fun (_ : ℝ≥0) => E)
      (LevyFoundations.finiteDimDistribution X μ) := by sorry
