-- Prove2me | Theorems.Thm_card_rest
-- name    : card_rest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:34.926078+00:00
-- url     : https://prove2.me/theorems/87d80f24-c895-41ed-94d4-ef0cac6e0755
-- title:
--   card rest: card rest
-- statement:
--   The card rest construction uses the card rest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L109-L117
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L109-L117

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}

theorem card_rest (hne : x ≠ y) :
    Fintype.card {z : α // z ≠ x ∧ z ≠ y} = Fintype.card α - 2 := by sorry
