-- Prove2me | Theorems.Thm_levy_foundations_finiteTail
-- name    : levy_foundations_finiteTail
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:34:39.300316+00:00
-- url     : https://prove2.me/theorems/d7c1cb98-f9d6-4c26-bae4-b9f1c51f8f75
-- title:
--   Finite mass of jumps exceeding a positive threshold
-- statement:
--   Every Lévy measure has finite intensity outside any neighbourhood of the origin. The lower threshold ε must be strictly positive.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L71-L94. A tail-finiteness consequence of Lévy-integrability. The new Prove2Me theorem requires its own accepted proof and statement audit.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory

theorem levy_foundations_finiteTail (ν : Measure ℝ)
    (hν : LevyFoundations.isLevyMeasure ν) {ε : ℝ} (hε : 0 < ε) :
    ν {x : ℝ | ε ≤ |x|} < ⊤ := by
  sorry
