-- Prove2me | Theorems.Thm_seqLiminf_eq_filter_liminfEReal
-- name    : seqLiminf_eq_filter_liminfEReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:54:30.261962+00:00
-- url     : https://prove2.me/theorems/62af1e7f-aa8a-46ff-a4f0-0a74122c8e03
-- title:
--   04_thm_4_8: seqLiminf_eq_filter_liminfEReal
-- statement:
--   Original source theorem `seqLiminf_eq_filter_liminfEReal` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_8.lean

import Definitions.Def_ProbabilityTheory_chapter_04_def_4_3_limsup_liminf_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic
open MeasureTheory
open scoped Topology

theorem seqLiminf_eq_filter_liminfEReal (u : ℕ → EReal) :
    seqLiminf u = Filter.liminf u Filter.atTop := by
  sorry
