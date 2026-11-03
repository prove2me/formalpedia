-- Prove2me | Theorems.Thm_levy_foundations_prmFinite
-- name    : levy_foundations_prmFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:06.171914+00:00
-- url     : https://prove2.me/theorems/a98032fd-6ad6-4569-bb70-3aca7795e8a4
-- title:
--   Every sigma-finite partition piece has finite measure
-- statement:
--   Each piece of the disjointed sigma-finite exhaustion has finite intensity.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L128-L131. Finite mass. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Definitions.Def_levy_foundations_prmPiece

open MeasureTheory Set

theorem levy_foundations_prmFinite
    {E : Type*} [MeasurableSpace E] (m : Measure E)
    [SigmaFinite m] (k : ℕ) :
    m (LevyFoundations.prmPiece m k) < ⊤ := by sorry
