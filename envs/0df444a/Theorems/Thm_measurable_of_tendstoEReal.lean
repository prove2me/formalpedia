-- Prove2me | Theorems.Thm_measurable_of_tendstoEReal
-- name    : measurable_of_tendstoEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:54:40.76853+00:00
-- url     : https://prove2.me/theorems/1d584711-592c-406d-9658-e4780b5c2d8a
-- title:
--   04_thm_4_8: measurable_of_tendstoEReal
-- statement:
--   Original source theorem `measurable_of_tendstoEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem measurable_of_tendstoEReal {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable g := by
  sorry
