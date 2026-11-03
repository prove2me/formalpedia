-- Prove2me | Theorems.Thm_levy_foundations_integralPieceMarksProduct
-- name    : levy_foundations_integralPieceMarksProduct
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:36:08.081446+00:00
-- url     : https://prove2.me/theorems/fd8174aa-a527-42c5-b22b-3236122b62db
-- title:
--   Expected product of finitely many independent identically distributed marks
-- statement:
--   For j independent marks of a single Poisson piece, the expectation of the complex product of bounded measurable mark weights equals the jth power of the expected mark weight.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Target requires remote Lean elaboration.  Source lines 947–969.

import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_independentPieceMarks

open MeasureTheory ProbabilityTheory

theorem levy_foundations_integralPieceMarksProduct
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) (w : E → ℂ) (hw : Measurable w)
    (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range j, w (X k n ω) ∂μ =
      (∫ x, w x ∂(LevyFoundations.prmPieceLaw m k)) ^ j := by sorry
