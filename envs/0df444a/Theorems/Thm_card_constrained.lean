-- Prove2me | Theorems.Thm_card_constrained
-- name    : card_constrained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:38.467209+00:00
-- url     : https://prove2.me/theorems/9eecd77f-9b88-572d-b4af-49b0bb437a1b
-- title:
--   card constrained: card constrained
-- statement:
--   The card constrained construction uses the card constrained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L152-L165
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L152-L165

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

theorem card_constrained (hne : x ≠ y) :
    ncard {U : Set α | x ∈ U → y ∈ U} ≤ 3 * 2 ^ (Fintype.card α - 2) := by sorry
