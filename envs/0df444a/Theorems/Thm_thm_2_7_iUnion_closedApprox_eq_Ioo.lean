-- Prove2me | Theorems.Thm_thm_2_7_iUnion_closedApprox_eq_Ioo
-- name    : thm_2_7_iUnion_closedApprox_eq_Ioo
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:13:16.707664+00:00
-- url     : https://prove2.me/theorems/3fa2c09b-4f98-4288-9b32-07808cd621ba
-- title:
--   ProbabilityTheory_chapter_02_thm_2_7_F000: thm_2_7_iUnion_closedApprox_eq_Ioo
-- statement:
--   Source theorem `thm_2_7_iUnion_closedApprox_eq_Ioo` extracted from `ProbabilityTheory.chapter_02.thm_2_7`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_7.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory

theorem thm_2_7_iUnion_closedApprox_eq_Ioo {a b : ℝ} (_hab : a < b) :
    (⋃ n : ℕ, thm_2_7_closedApprox a b n) = Set.Ioo a b := by
  sorry
