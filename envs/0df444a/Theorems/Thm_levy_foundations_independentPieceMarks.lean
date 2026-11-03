-- Prove2me | Theorems.Thm_levy_foundations_independentPieceMarks
-- name    : levy_foundations_independentPieceMarks
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:20:33.155251+00:00
-- url     : https://prove2.me/theorems/f69986ab-4769-4341-9643-1451ec47712b
-- title:
--   Mutual independence of marks within a fixed Poisson piece
-- statement:
--   Joint independence of the combined count-and-mark family restricts to mutual independence of all marked points from any one partition piece.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Target requires remote Lean elaboration.  Source lines 288–291.

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory

theorem levy_foundations_independentPieceMarks
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) :
    iIndepFun (fun n => X k n) μ := by sorry
