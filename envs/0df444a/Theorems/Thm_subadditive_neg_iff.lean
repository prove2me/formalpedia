-- Prove2me | Theorems.Thm_subadditive_neg_iff
-- name    : subadditive_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:09.72349+00:00
-- url     : https://prove2.me/theorems/0b1794a8-ecf1-4871-9d03-f67e059b9ef4
-- title:
--   subadditive neg iff: subadditive neg iff
-- statement:
--   The subadditive neg iff construction uses the subadditive neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L111-L112
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L111-L112

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology

theorem subadditive_neg_iff {u : ℕ → ℝ} : (Subadditive fun n ↦ -u n) ↔ Superadditive u := by sorry
