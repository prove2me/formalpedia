-- Prove2me | Theorems.Thm_measurable_seqInfEReal
-- name    : measurable_seqInfEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:52:31.102492+00:00
-- url     : https://prove2.me/theorems/221babb0-e3f4-4722-ba8f-25a9bc04da40
-- title:
--   04_thm_4_7: measurable_seqInfEReal
-- statement:
--   Original source theorem `measurable_seqInfEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_7.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_sup_inf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory

theorem measurable_seqInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i))
  : Measurable (fun ω => seqInf (fun i => f i ω)) := by
  sorry
