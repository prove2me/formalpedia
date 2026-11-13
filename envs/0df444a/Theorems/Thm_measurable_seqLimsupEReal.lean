-- Prove2me | Theorems.Thm_measurable_seqLimsupEReal
-- name    : measurable_seqLimsupEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:53:43.915573+00:00
-- url     : https://prove2.me/theorems/5cbda49e-73f0-4a6d-82cb-874e985d4fa7
-- title:
--   04_thm_4_8: measurable_seqLimsupEReal
-- statement:
--   Original source theorem `measurable_seqLimsupEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem measurable_seqLimsupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => seqLimsup (fun i => f i ω)) := by
  sorry
