-- Prove2me | Theorems.Thm_levy_foundations_partialNextVecIndependent
-- name    : levy_foundations_partialNextVecIndependent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:00:03.768747+00:00
-- url     : https://prove2.me/theorems/3271b33e-768a-4c9b-be43-4eef0cbf0d29
-- title:
--   Independence of a partial count vector and the next Poisson piece
-- statement:
--   The vector of counts from the first n+1 Poisson pieces and the vector from the next piece are independent, even when evaluated sets overlap within each vector. This allows characteristic functions to multiply inductively.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, indepFun_prmPartialCountVec_thinnedCountVec around line 774.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_prmPartialCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_prmPartialCountMeasurable
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

open MeasureTheory ProbabilityTheory

theorem levy_foundations_partialNextVecIndependent
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (n : ℕ) :
    IndepFun
      (fun ω (i : ι) => (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ))
      (fun ω (i : ι) => (LevyFoundations.thinnedCount K X (A i) (n + 1) ω : ℝ))
      μ := by sorry
