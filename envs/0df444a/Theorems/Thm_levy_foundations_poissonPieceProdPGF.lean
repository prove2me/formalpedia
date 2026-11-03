-- Prove2me | Theorems.Thm_levy_foundations_poissonPieceProdPGF
-- name    : levy_foundations_poissonPieceProdPGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:51:48.790748+00:00
-- url     : https://prove2.me/theorems/71911e07-1794-4a45-9e12-444e0067d6b5
-- title:
--   Generating functional of marks in a single Poisson piece
-- statement:
--   For bounded measurable complex mark weight w, the expectation of the product of weights over every realised mark in a Poisson piece is exp(λ(Ew−1)). The count and mark laws are those of the Poisson point family.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Draft target, full Lean elaboration outstanding.  Source lines 1010–1055; conditioning on the Poisson piece count.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_poissonPGFSeries
import Theorems.Thm_levy_foundations_integralPieceMarksProduct
import Theorems.Thm_levy_foundations_poissonCountCellIntegral
import Theorems.Thm_levy_foundations_pieceCountEventProb
import Theorems.Thm_levy_foundations_poissonPieceProductIntegrable

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_poissonPieceProdPGF
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) (w : E → ℂ)
    (hw : Measurable w) (hbdd : ∀ x, ‖w x‖ ≤ 1) :
    ∫ ω, ∏ n ∈ Finset.range (K k ω), w (X k n ω) ∂μ =
      Complex.exp
        ((m (LevyFoundations.prmPiece m k)).toReal *
          ((∫ x, w x ∂(LevyFoundations.prmPieceLaw m k)) - 1)) := by sorry
