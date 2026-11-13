-- Prove2me | Theorems.Thm_thm_4_7
-- name    : thm_4_7
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:52:43.234194+00:00
-- url     : https://prove2.me/theorems/152dfbbb-6623-4878-a9f4-dc6c85eda545
-- title:
--   04_thm_4_7: thm_4_7
-- statement:
--   Original source theorem `thm_4_7` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_7.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory

theorem thm_4_7 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => seqSup (fun i => f i ω)) ∧
      Measurable (fun ω => seqInf (fun i => f i ω)) := by
  sorry
