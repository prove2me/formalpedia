-- Prove2me | Theorems.Thm_levy_foundations_compensatedPieceSumVariance
-- name    : levy_foundations_compensatedPieceSumVariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T15:17:38.070216+00:00
-- url     : https://prove2.me/theorems/93c89c43-1777-4f5d-a11c-7eecfecd07ed
-- title:
--   Second-moment isometry on an intensity piece
-- statement:
--   The compensated piece sum has variance equal to the intensity integral of the squared integrand restricted to that piece.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean#L121-L126. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_compensatedPieceSum
import Definitions.Def_levy_foundations_prmPiece

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_compensatedPieceSumVariance
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E) (f : E → ℝ) (k : ℕ)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, (LevyFoundations.compensatedPieceSum m K X f k ω) ^ 2 ∂μ =
      ∫ x in LevyFoundations.prmPiece m k, f x ^ 2 ∂m := by sorry
