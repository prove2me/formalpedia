-- Prove2me | Theorems.Thm_levy_foundations_prmCountLaw
-- name    : levy_foundations_prmCountLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T15:16:45.780989+00:00
-- url     : https://prove2.me/theorems/c9c702fe-3174-4bf2-97df-232295412e4c
-- title:
--   Poisson law of a finite-intensity random-measure evaluation
-- statement:
--   For each measurable finite-intensity set A, the random measure's count of A has Poisson distribution with mean m(A), expressed as an ENNReal-valued count.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L438-L456. Poisson count superposition and marking law. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmCountLaw
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    μ.map (fun ω => LevyFoundations.poissonRandomMeasure K X ω A) =
      (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ENNReal) := by sorry
