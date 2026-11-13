-- Prove2me | Theorems.Thm_thm_6_3
-- name    : thm_6_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:01:16.823481+00:00
-- url     : https://prove2.me/theorems/a7ee2d6c-5cb2-4384-9a79-c99e95d8ecec
-- title:
--   ProbabilityTheory_chapter_06_thm_6_3_F000: thm_6_3
-- statement:
--   Source theorem `thm_6_3` extracted from `ProbabilityTheory.chapter_06.thm_6_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_3.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem thm_6_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : X ≤ Y) :
    ∫⁻ ω, X ω ∂μ ≤ ∫⁻ ω, Y ω ∂μ := by
  sorry
