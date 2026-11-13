-- Prove2me | Theorems.Thm_ex_6_1_2
-- name    : ex_6_1_2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:04:01.946009+00:00
-- url     : https://prove2.me/theorems/2b438571-4ed2-4763-8898-d8edd7b38e8b
-- title:
--   Chapter 6, ex_6_1_2: ex_6_1_2
-- statement:
--   Source theorem `ex_6_1_2` from Chapter 6, module `ex_6_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/ex_6_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

theorem ex_6_1_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (B : Set Ω)
    (hB : MeasurableSet B) :
    Measurable
        (((SimpleFunc.const Ω (1 : EReal)).restrict B : SimpleFunc Ω EReal) : Ω → EReal) ∧
      ∀ {x : EReal},
        def_6_2 μ ((SimpleFunc.const Ω (1 : EReal)).restrict B) = some x →
        x = (μ B : EReal) := by sorry
