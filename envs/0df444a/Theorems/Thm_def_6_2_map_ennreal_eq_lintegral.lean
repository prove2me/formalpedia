-- Prove2me | Theorems.Thm_def_6_2_map_ennreal_eq_lintegral
-- name    : def_6_2_map_ennreal_eq_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:52:20.639437+00:00
-- url     : https://prove2.me/theorems/58261ef1-b56a-45b3-a1aa-af1a5352e22a
-- title:
--   Source theorem: def_6_2_map_ennreal_eq_lintegral
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

theorem def_6_2_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    def_6_2 μ (X.map fun x : ENNReal => (x : EReal)) =
      some ((X.lintegral μ : ENNReal) : EReal) := by
  sorry
