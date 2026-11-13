-- Prove2me | Theorems.Thm_measurable_tailInfEReal
-- name    : measurable_tailInfEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:53:20.61198+00:00
-- url     : https://prove2.me/theorems/919bd13b-9afb-4332-9695-e4f273e8744c
-- title:
--   04_thm_4_8: measurable_tailInfEReal
-- statement:
--   Original source theorem `measurable_tailInfEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem measurable_tailInfEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    Measurable (fun ω => tailInf (fun i => f i ω) n) := by
  sorry
