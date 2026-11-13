-- Prove2me | Theorems.Thm_generatedSigmaField_contains
-- name    : generatedSigmaField_contains
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:08:50.469398+00:00
-- url     : https://prove2.me/theorems/1e3f05b0-92d6-419c-942a-4fe8f41d0ec3
-- title:
--   ProbabilityTheory_chapter_02_def_2_7_F000: generatedSigmaField_contains
-- statement:
--   Source theorem `generatedSigmaField_contains` extracted from `ProbabilityTheory.chapter_02.def_2_7`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_7.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_7_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory

theorem generatedSigmaField_contains {Ω : Type*} (C : Set (Set Ω)) :
    ∀ s ∈ C, @MeasurableSet Ω (generatedSigmaField C) s := by
  sorry
