-- Prove2me | Theorems.Thm_thm_2_4_tsum_eq_iSup_sum_range_succ
-- name    : thm_2_4_tsum_eq_iSup_sum_range_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:20:30.712397+00:00
-- url     : https://prove2.me/theorems/4d5848bd-95d4-4f78-93dc-11dd3b9fa795
-- title:
--   02_thm_2_4: thm_2_4_tsum_eq_iSup_sum_range_succ
-- statement:
--   Original source theorem `thm_2_4_tsum_eq_iSup_sum_range_succ` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_4_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set
open scoped BigOperators

theorem thm_2_4_tsum_eq_iSup_sum_range_succ (f : ℕ → ENNReal) :
    ∑' i, f i = ⨆ n, ∑ i ∈ Finset.range (n + 1), f i := by
  sorry
