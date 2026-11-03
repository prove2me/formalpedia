-- Prove2me | Theorems.Thm_levy_foundations_thinnedCountToENNReal
-- name    : levy_foundations_thinnedCountToENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:32:44.666531+00:00
-- url     : https://prove2.me/theorems/08f65e84-50f6-4fc1-8e69-da615b056429
-- title:
--   Thinned piece counts equal finite sums of membership indicators
-- statement:
--   The ENNReal cast of the number of marked points in A among the first K(k,ω) marks equals the finite sum of their membership indicators.
-- source:
--   Inspired by Shmuel Link, LeanLevy, MIT licence, frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean lines 72–112. Independently authored draft for pinned Prove2Me Mathlib; compiler verification outstanding.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_thinnedCount

open MeasureTheory Set
open scoped ENNReal

theorem levy_foundations_thinnedCountToENNReal
    {Ω E : Type*} (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (A : Set E)
    (k : ℕ) (ω : Ω) :
    (LevyFoundations.thinnedCount K X A k ω : ℝ≥0∞) =
      ∑ n ∈ Finset.range (K k ω),
        A.indicator (1 : E → ℝ≥0∞) (X k n ω) := by sorry
