-- Prove2me | Theorems.Thm_thm_4_1
-- name    : thm_4_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:49:39.816208+00:00
-- url     : https://prove2.me/theorems/05c4bf45-4d97-4309-adfd-29de9f69b279
-- title:
--   Chapter 4, thm_4_1
-- statement:
--   Supporting Lean declarations for Chapter 4, source module `thm_4_1`: `thm_4_1`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_1.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_2_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic

theorem thm_4_1 {Ω : Type _} [MeasurableSpace Ω] (A : Set Ω) :
    Measurable (Set.indicator A (fun _ => (1 : ℝ))) ↔ MeasurableSet A := by
  sorry
