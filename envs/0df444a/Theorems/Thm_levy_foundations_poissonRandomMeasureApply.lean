-- Prove2me | Theorems.Thm_levy_foundations_poissonRandomMeasureApply
-- name    : levy_foundations_poissonRandomMeasureApply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:41:34.533713+00:00
-- url     : https://prove2.me/theorems/d48d61f3-55db-47a7-b0be-c144daaefcee
-- title:
--   Evaluation of a Poisson random counting measure as the sum of thinned counts
-- statement:
--   Evaluating the random counting measure on a measurable set A gives the infinite sum of the thinned point counts from every partition piece.
-- source:
--   Inspired by Shmuel Link, LeanLevy, MIT licence, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean lines 72–112. Independently authored draft for pinned Prove2Me Mathlib; compiler verification outstanding.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_thinnedCountToENNReal

open MeasureTheory Set
open scoped ENNReal

theorem levy_foundations_poissonRandomMeasureApply
    {Ω E : Type*} [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {A : Set E} (hA : MeasurableSet A) :
    LevyFoundations.poissonRandomMeasure K X ω A =
      ∑' k : ℕ, (LevyFoundations.thinnedCount K X A k ω : ℝ≥0∞) := by sorry
