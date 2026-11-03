-- Prove2me | Theorems.Thm_levy_foundations_thinnedCountPGF
-- name    : levy_foundations_thinnedCountPGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:07:04.872061+00:00
-- url     : https://prove2.me/theorems/0ad93e2c-55fe-45bb-b069-c6c192dc5532
-- title:
--   Probability-generating identity for one thinned Poisson count
-- statement:
--   The generating function E[z^N] of the number of marks in A in one Poisson piece equals exp(m(piece∩A)(z−1)) when |z|≤1.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Draft target, full Lean elaboration outstanding.  Source lines 1068–1102; substitute the two-valued mark weight into the piece generating functional.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_levy_foundations_prodIteConstCard
import Theorems.Thm_levy_foundations_prmPieceLawProb
import Definitions.Def_levy_foundations_thinnedCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_thinnedCountPGF
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) {A : Set E} (hA : MeasurableSet A)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∫ ω, z ^ (LevyFoundations.thinnedCount K X A k ω) ∂μ =
      Complex.exp
        ((m (LevyFoundations.prmPiece m k ∩ A)).toReal * (z - 1)) := by sorry
