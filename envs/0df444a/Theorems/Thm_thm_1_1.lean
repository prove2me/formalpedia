-- Prove2me | Theorems.Thm_thm_1_1
-- name    : thm_1_1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:11:28.947167+00:00
-- url     : https://prove2.me/theorems/cc7c6191-b741-4b7e-8e8e-68c66965d51a
-- title:
--   Chapter 1, thm_1_1: thm_1_1
-- statement:
--   Source theorem `thm_1_1` from Chapter 1, module `thm_1_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.Order.ProjIcc

open Finset BigOperators
open Set Topology

noncomputable section

theorem thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : MonotoneOn α (Icc a b))
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b →
      ContinuousWithinAt α (Icc a b) x) :
    RSIntegrable f α a b := by sorry
