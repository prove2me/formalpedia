-- Prove2me | Theorems.Thm_levy_foundations_sigmaFinite
-- name    : levy_foundations_sigmaFinite
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:34:56.44598+00:00
-- url     : https://prove2.me/theorems/98086eea-50d4-4f3f-b70a-ba0fcbdd6158
-- title:
--   Every Lévy measure is sigma-finite
-- statement:
--   A Lévy measure on the real line can be exhausted by a countable cover of measurable sets of finite measure, using its finite intensity away from zero and its zero atom at zero.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L100-L120. Sigma-finiteness of Lévy jump intensity. The new Prove2Me theorem requires its own accepted proof and statement audit.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory

theorem levy_foundations_sigmaFinite (ν : Measure ℝ)
    (hν : LevyFoundations.isLevyMeasure ν) : SigmaFinite ν := by
  sorry
