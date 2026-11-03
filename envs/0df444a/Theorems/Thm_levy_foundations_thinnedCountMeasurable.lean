-- Prove2me | Theorems.Thm_levy_foundations_thinnedCountMeasurable
-- name    : levy_foundations_thinnedCountMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:09:08.553519+00:00
-- url     : https://prove2.me/theorems/a71dc135-d1a2-4eca-9cec-57861b5f6d92
-- title:
--   Measurability of a finite-piece thinned count
-- statement:
--   A finite-piece count is measurable when its piece count and all marks are measurable and the marked set is measurable.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean, measurable_thinnedCount at line 939.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_thinnedCount

open MeasureTheory

theorem levy_foundations_thinnedCountMeasurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (k : ℕ) (hK : Measurable (K k))
    (hX : ∀ n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable (LevyFoundations.thinnedCount K X A k) := by sorry
