-- Prove2me | Theorems.Thm_measurable_seqLiminfEReal
-- name    : measurable_seqLiminfEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:53:59.188211+00:00
-- url     : https://prove2.me/theorems/45d847cf-0fd0-41a2-9ff2-c1b942a5acb0
-- title:
--   04_thm_4_8: measurable_seqLiminfEReal
-- statement:
--   Original source theorem `measurable_seqLiminfEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem measurable_seqLiminfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLiminf (fun i => f i ω)) := by
  sorry
