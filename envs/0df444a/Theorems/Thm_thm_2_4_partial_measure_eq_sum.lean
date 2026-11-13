-- Prove2me | Theorems.Thm_thm_2_4_partial_measure_eq_sum
-- name    : thm_2_4_partial_measure_eq_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:20:14.135625+00:00
-- url     : https://prove2.me/theorems/c1ddcd0e-838a-4303-bc49-e4cb8c871106
-- title:
--   02_thm_2_4: thm_2_4_partial_measure_eq_sum
-- statement:
--   Original source theorem `thm_2_4_partial_measure_eq_sum` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_partial_measure_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : ℕ → Set Ω)
    (hA : SetSeqIncreasing A) (hAmeas : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    μ (A n) = ∑ i ∈ Finset.range (n + 1), μ (thm_2_4_increment A i) := by
  sorry
