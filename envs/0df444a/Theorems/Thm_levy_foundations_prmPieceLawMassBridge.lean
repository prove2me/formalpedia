-- Prove2me | Theorems.Thm_levy_foundations_prmPieceLawMassBridge
-- name    : levy_foundations_prmPieceLawMassBridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:35:26.33517+00:00
-- url     : https://prove2.me/theorems/89176b50-e42b-4ef5-9aae-d4fc515d65a6
-- title:
--   Intensity factorisation through a normalised mark law
-- statement:
--   The mass of the kth Poisson piece times its normalised probability of A equals the intensity assigned to the intersection of that piece with A. This includes the zero-mass case.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Draft target, full Lean elaboration outstanding.  Source lines 1058–1066.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_prmPieceLawOfNonzero
import Theorems.Thm_levy_foundations_prmFinite

open MeasureTheory

theorem levy_foundations_prmPieceLawMassBridge
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ)
    {A : Set E} (hA : MeasurableSet A) :
    (m (LevyFoundations.prmPiece m k)).toReal *
      (LevyFoundations.prmPieceLaw m k).real A =
      (m (LevyFoundations.prmPiece m k ∩ A)).toReal := by sorry
