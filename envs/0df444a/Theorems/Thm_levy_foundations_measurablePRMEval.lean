-- Prove2me | Theorems.Thm_levy_foundations_measurablePRMEval
-- name    : levy_foundations_measurablePRMEval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:49:54.898177+00:00
-- url     : https://prove2.me/theorems/ace77574-ad25-4e6a-9a28-ea8f763ab98c
-- title:
--   Measurability of Poisson random-measure set evaluations
-- statement:
--   If every count and point mark is measurable, evaluating the constructed counting measure on a measurable set gives a measurable random variable.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L107-L112. Random-measure evaluation measurability. Independently authored Prove2Me draft pending statement audit and remote compilation.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Theorems.Thm_levy_foundations_poissonRandomMeasureApply
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

open MeasureTheory

theorem levy_foundations_measurablePRMEval
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n))
    {A : Set E} (hA : MeasurableSet A) :
    Measurable (fun ω => LevyFoundations.poissonRandomMeasure K X ω A) := by sorry
