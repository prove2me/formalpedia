-- Prove2me | Theorems.Thm_levy_foundations_independentPieceCountMarks
-- name    : levy_foundations_independentPieceCountMarks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:20:33.525247+00:00
-- url     : https://prove2.me/theorems/75b055c5-11cf-4a76-adc8-0b6cba0e9f64
-- title:
--   Poisson count independent of all marks from the same piece
-- statement:
--   The Poisson count K(k) is independent of the entire sequence of marks in the same piece, as a measurable countable product-valued random variable.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Target requires remote Lean elaboration.  Source lines 352–359.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory

theorem levy_foundations_independentPieceCountMarks
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) :
    IndepFun (K k) (fun ω n => X k n ω) μ := by sorry
