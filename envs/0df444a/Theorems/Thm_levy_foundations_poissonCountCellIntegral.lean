-- Prove2me | Theorems.Thm_levy_foundations_poissonCountCellIntegral
-- name    : levy_foundations_poissonCountCellIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:36:14.119992+00:00
-- url     : https://prove2.me/theorems/84be0069-b19e-470f-a5a8-b2eaea8bfc3b
-- title:
--   Factorisation of a mark functional on a Poisson-count event
-- statement:
--   Integrating a measurable complex functional of the entire marked sequence over the event K(k)=j factorises into the probability of that count event and the unconditional mark-functional expectation.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Target requires remote Lean elaboration.  Source lines 971–1006.

import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_independentPieceCountMarks

open MeasureTheory ProbabilityTheory

theorem levy_foundations_poissonCountCellIntegral
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) (ψ : (ℕ → E) → ℂ)
    (hψ : Measurable ψ) :
    ∫ ω in {ω | K k ω = j}, ψ (fun n => X k n ω) ∂μ =
      (μ.real {ω | K k ω = j} : ℂ) *
        ∫ ω, ψ (fun n => X k n ω) ∂μ := by sorry
