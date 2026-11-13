-- Prove2me | Theorems.Thm_measurable_tailSupEReal
-- name    : measurable_tailSupEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:52:58.593206+00:00
-- url     : https://prove2.me/theorems/e24d6be6-7197-448b-b0a9-63db6395852f
-- title:
--   04_thm_4_8: measurable_tailSupEReal
-- statement:
--   Original source theorem `measurable_tailSupEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem measurable_tailSupEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailSup (fun i => f i ω) n) := by
  sorry
