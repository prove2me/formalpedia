-- Prove2me | Theorems.Thm_seqLimsup_eq_filter_limsupEReal
-- name    : seqLimsup_eq_filter_limsupEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:54:11.371362+00:00
-- url     : https://prove2.me/theorems/09ed5f24-2cce-4584-9b16-dc1c07120352
-- title:
--   04_thm_4_8: seqLimsup_eq_filter_limsupEReal
-- statement:
--   Original source theorem `seqLimsup_eq_filter_limsupEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem seqLimsup_eq_filter_limsupEReal (u : ℕ → EReal) :
    seqLimsup u = Filter.limsup u Filter.atTop := by
  sorry
