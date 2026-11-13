-- Prove2me | Theorems.Thm_indicatorRepresentationIntegral_succ
-- name    : indicatorRepresentationIntegral_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:51:02.494872+00:00
-- url     : https://prove2.me/theorems/f97608ae-621f-4bf6-b88f-32ff14299d4f
-- title:
--   Source theorem: indicatorRepresentationIntegral_succ
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

theorem indicatorRepresentationIntegral_succ (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationIntegral (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegral (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  sorry
