-- Prove2me | Theorems.Thm_indicatorRepresentationSimpleFunction_succ
-- name    : indicatorRepresentationSimpleFunction_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:50:36.269205+00:00
-- url     : https://prove2.me/theorems/e8f45e94-5553-495f-9e0d-7b53192f0138
-- title:
--   Source theorem: indicatorRepresentationSimpleFunction_succ
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

theorem indicatorRepresentationSimpleFunction_succ
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B =
      indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0 +
        indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ) := by
  sorry
