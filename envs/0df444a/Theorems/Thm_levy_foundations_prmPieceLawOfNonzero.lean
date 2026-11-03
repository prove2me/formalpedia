-- Prove2me | Theorems.Thm_levy_foundations_prmPieceLawOfNonzero
-- name    : levy_foundations_prmPieceLawOfNonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:00:50.85696+00:00
-- url     : https://prove2.me/theorems/6641dc12-4387-449a-b58f-46cbb88c8e82
-- title:
--   Explicit normalisation of a positive-mass Poisson partition piece
-- statement:
--   If partition piece k has positive intensity, its mark law equals the restriction of intensity to the piece, scaled by the reciprocal of its mass. The separate zero-mass Dirac branch is excluded by the hypothesis.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean. Draft target, full Lean elaboration outstanding.  Source lines 136–139.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw

open MeasureTheory

theorem levy_foundations_prmPieceLawOfNonzero
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ)
    (hk : m (LevyFoundations.prmPiece m k) ≠ 0) :
    LevyFoundations.prmPieceLaw m k =
      (m (LevyFoundations.prmPiece m k))⁻¹ •
        m.restrict (LevyFoundations.prmPiece m k) := by sorry
