-- Prove2me | Theorems.Thm_simpleFunctionIntegralValue_map_ennreal_eq_lintegral
-- name    : simpleFunctionIntegralValue_map_ennreal_eq_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:52:01.00156+00:00
-- url     : https://prove2.me/theorems/80a21d78-5f32-413c-b09b-a6cce621af3b
-- title:
--   Source theorem: simpleFunctionIntegralValue_map_ennreal_eq_lintegral
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

theorem simpleFunctionIntegralValue_map_ennreal_eq_lintegral
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal)) =
      ((X.lintegral μ : ENNReal) : EReal) := by
  sorry
