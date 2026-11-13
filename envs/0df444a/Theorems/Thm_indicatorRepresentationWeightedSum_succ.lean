-- Prove2me | Theorems.Thm_indicatorRepresentationWeightedSum_succ
-- name    : indicatorRepresentationWeightedSum_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:50:48.48306+00:00
-- url     : https://prove2.me/theorems/b0b26539-4fb5-465e-b3d5-edc53218a9b3
-- title:
--   Source theorem: indicatorRepresentationWeightedSum_succ
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_06.def_6_2, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem indicatorRepresentationWeightedSum_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationWeightedSum (Ω := Ω) μ (n + 1) b B =
      textbookIntegralAdd
        (some (b 0 * (μ (B 0) : EReal)))
        (indicatorRepresentationWeightedSum (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ)) := by
  sorry
