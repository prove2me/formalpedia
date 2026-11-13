-- Prove2me | Theorems.Thm_thm_2_4_countable_additivity_spine
-- name    : thm_2_4_countable_additivity_spine
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:20:43.076839+00:00
-- url     : https://prove2.me/theorems/f6ce58c4-f36d-47a7-b336-1ab350dfdba8
-- title:
--   02_thm_2_4: thm_2_4_countable_additivity_spine
-- statement:
--   Original source theorem `thm_2_4_countable_additivity_spine` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_countable_additivity_spine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) :
    μ (⋃ i, A i) = ∑' i, μ (thm_2_4_increment A i) := by
  sorry
