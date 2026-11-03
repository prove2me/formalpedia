-- Prove2me | Theorems.Thm_levy_foundations_prmPieceLawProb
-- name    : levy_foundations_prmPieceLawProb
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:56:11.230009+00:00
-- url     : https://prove2.me/theorems/0f16c439-c4ed-4f6a-a606-ffbee35d55c4
-- title:
--   Normalised partition-piece laws are probability measures
-- statement:
--   The normalised nonzero-mass law and the fallback Dirac law both have total mass one.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L141-L150. Probability measure proof. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw
import Theorems.Thm_levy_foundations_prmFinite

open MeasureTheory

theorem levy_foundations_prmPieceLawProb
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ) :
    IsProbabilityMeasure (LevyFoundations.prmPieceLaw m k) := by sorry
