-- Prove2me | Theorems.Thm_ereal_coe_finset_sum__138bdd
-- name    : ereal_coe_finset_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:03:13.653261+00:00
-- url     : https://prove2.me/theorems/138bdd00-3716-425e-98da-a15664bdb4a5
-- title:
--   ProbabilityTheory_chapter_06_def_6_2_F000: ereal_coe_finset_sum
-- statement:
--   Source theorem `ereal_coe_finset_sum` extracted from `ProbabilityTheory.chapter_06.def_6_2`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ENNReal) :
    ((∑ i ∈ s, f i : ENNReal) : EReal) = ∑ i ∈ s, ((f i : ENNReal) : EReal) := by
  sorry
