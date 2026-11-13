-- Prove2me | Theorems.Thm_simpleFunctionIntegralDefined_map_ennreal
-- name    : simpleFunctionIntegralDefined_map_ennreal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:51:49.587633+00:00
-- url     : https://prove2.me/theorems/90112ca5-6215-4fd9-b077-13dfe3796387
-- title:
--   Source theorem: simpleFunctionIntegralDefined_map_ennreal
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

theorem simpleFunctionIntegralDefined_map_ennreal
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    simpleFunctionIntegralDefined μ (X.map fun x : ENNReal => (x : EReal)) := by
  sorry
