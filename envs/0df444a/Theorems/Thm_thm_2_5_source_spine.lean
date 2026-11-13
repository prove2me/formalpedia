-- Prove2me | Theorems.Thm_thm_2_5_source_spine
-- name    : thm_2_5_source_spine
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:53:50.901323+00:00
-- url     : https://prove2.me/theorems/46e9543d-f364-46f5-ab99-30a1a88e2f05
-- title:
--   Source theorem: thm_2_5_source_spine
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_02.thm_2_5, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_5.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set

theorem thm_2_5_source_spine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Set Ω) (hA : SetSeqDecreasing A)
    (hMeas : ∀ i, MeasurableSet (A i)) (hfin : μ (A 0) < ⊤) :
    μ (⋂ i, A i) = ⨅ i, μ (A i) := by
  sorry
