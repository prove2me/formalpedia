-- Prove2me | Theorems.Thm_levy_foundations_pieceCountEventProb
-- name    : levy_foundations_pieceCountEventProb
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:36:18.479088+00:00
-- url     : https://prove2.me/theorems/9c43664e-cc29-47d2-99fb-35db2bd03ba5
-- title:
--   Exact-count event has the prescribed Poisson probability
-- statement:
--   The probability of observing exactly j points in the kth partition piece is the mass of j under the Poisson law with rate m(piece k), as given by the count marginal of the point-family predicate.
-- source:
--   Inspired by LeanLevy, PoissonPointFamily.lean lines 520–526, MIT licence, commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Draft pending remote Lean verification.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory

theorem levy_foundations_pieceCountEventProb
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) :
    μ.real {ω | K k ω = j} =
      (poissonMeasure (m (LevyFoundations.prmPiece m k)).toNNReal).real {j} := by sorry
