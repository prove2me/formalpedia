-- Prove2me | Theorems.Thm_thm_6_2
-- name    : thm_6_2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:27:26.906135+00:00
-- url     : https://prove2.me/theorems/716cbe9e-5d83-487e-8d36-838eb1c27153
-- title:
--   Chapter 6, thm_6_2: thm_6_2
-- statement:
--   Source theorem `thm_6_2` from Chapter 6, module `thm_6_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

theorem thm_6_2 (μ : Measure Ω) :
    ∀ (n : ℕ) (b : Fin n → EReal) (B : Fin n → Set Ω),
      (∀ i, MeasurableSet (B i)) →
      Measurable
          (((indicatorRepresentationSimpleFunction (Ω := Ω) n b B : SimpleFunc Ω EReal) :
            Ω → EReal)) ∧
        ∀ {x : EReal},
          indicatorRepresentationIntegral (Ω := Ω) μ n b B = some x →
          def_6_2 μ (indicatorRepresentationSimpleFunction (Ω := Ω) n b B) = some x := by sorry
