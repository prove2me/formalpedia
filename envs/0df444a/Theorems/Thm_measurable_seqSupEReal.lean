-- Prove2me | Theorems.Thm_measurable_seqSupEReal
-- name    : measurable_seqSupEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:52:15.350184+00:00
-- url     : https://prove2.me/theorems/65cb77b7-f089-49ea-99f0-9c9cdb4d3c9f
-- title:
--   04_thm_4_7: measurable_seqSupEReal
-- statement:
--   Original source theorem `measurable_seqSupEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_7.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory

theorem measurable_seqSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqSup (fun i => f i ω)) := by
  sorry
