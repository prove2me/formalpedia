-- Prove2me | Theorems.Thm_generatedSigmaFieldSeq_contains
-- name    : generatedSigmaFieldSeq_contains
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:09:10.226752+00:00
-- url     : https://prove2.me/theorems/edb71ef1-3744-4fec-88bf-d20e0d5e925a
-- title:
--   ProbabilityTheory_chapter_02_def_2_7_F000: generatedSigmaFieldSeq_contains
-- statement:
--   Source theorem `generatedSigmaFieldSeq_contains` extracted from `ProbabilityTheory.chapter_02.def_2_7`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_7.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory

theorem generatedSigmaFieldSeq_contains {Ω : Type*} (B : ℕ → Set Ω) (n : ℕ) :
    @MeasurableSet Ω (generatedSigmaFieldSeq B) (B n) := by
  sorry
