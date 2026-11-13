-- Prove2me | Theorems.Thm_simpleFunctionIntegralFinChain_succ
-- name    : simpleFunctionIntegralFinChain_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:50:19.425203+00:00
-- url     : https://prove2.me/theorems/45fd10aa-4aa8-4852-af66-4196534a2dd8
-- title:
--   Source theorem: simpleFunctionIntegralFinChain_succ
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

theorem simpleFunctionIntegralFinChain_succ (μ : Measure Ω) (n : ℕ)
    (F : Fin (n + 1) → SimpleFunc Ω EReal) :
    simpleFunctionIntegralFinChain μ (n + 1) F =
      match simpleFunctionIntegralFinChain μ n (fun i => F i.succ) with
      | some _ => simpleFunctionIntegralAdd μ (F 0) (∑ i : Fin n, F i.succ)
      | none => none := by
  sorry
