-- Prove2me | Theorems.Thm_card_valid_bases_dominated
-- name    : card_valid_bases_dominated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:20.262327+00:00
-- url     : https://prove2.me/theorems/514843c1-5ddf-5c08-8224-54cce6b95705
-- title:
--   card valid bases dominated: card valid bases dominated
-- statement:
--   The card valid bases dominated construction uses the card valid bases dominated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L319-L346
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L319-L346

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

theorem card_valid_bases_dominated (hN : 10 ≤ Fintype.card α) :
    Fintype.card (ValidBasis α) ≤
      2 * 2 ^ (2 ^ Fintype.card α - Fintype.card α) := by sorry
