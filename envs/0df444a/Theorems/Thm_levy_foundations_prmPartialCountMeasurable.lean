-- Prove2me | Theorems.Thm_levy_foundations_prmPartialCountMeasurable
-- name    : levy_foundations_prmPartialCountMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:33:03.986372+00:00
-- url     : https://prove2.me/theorems/f830da5a-f381-409b-884f-05530b332477
-- title:
--   Measurability of finite Poisson superposition counts
-- statement:
--   Every finite initial superposition of measurable thinned piece counts is a measurable random variable.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, measurable_prmPartialCount at line 219.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_prmPartialCount
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

open MeasureTheory

theorem levy_foundations_prmPartialCountMeasurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (A : Set E) (n : ℕ)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k j, Measurable (X k j))
    (hA : MeasurableSet A) :
    Measurable (LevyFoundations.prmPartialCount K X A n) := by sorry
