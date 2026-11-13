-- Prove2me | Theorems.Thm_thm_4_8
-- name    : thm_4_8
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:54:52.753718+00:00
-- url     : https://prove2.me/theorems/28724561-5ab2-461f-9973-e726fe31f9be
-- title:
--   04_thm_4_8: thm_4_8
-- statement:
--   Original source theorem `thm_4_8` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem thm_4_8 {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → EReal)
    (hf : ∀ i, Measurable (f i)) {g : Ω → EReal}
    (hg : ∀ ω, Filter.Tendsto (fun n => f n ω) Filter.atTop (𝓝 (g ω))) :
    Measurable (fun ω => seqLimsup (fun i => f i ω)) ∧
      Measurable (fun ω => seqLiminf (fun i => f i ω)) ∧
      Measurable g := by
  sorry
