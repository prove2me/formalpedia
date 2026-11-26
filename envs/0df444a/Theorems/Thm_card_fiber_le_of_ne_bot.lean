-- Prove2me | Theorems.Thm_card_fiber_le_of_ne_bot
-- name    : card_fiber_le_of_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:07.95821+00:00
-- url     : https://prove2.me/theorems/f367d649-c7d0-4847-ac54-9068af5412d8
-- title:
--   card fiber le of ne bot: card fiber le of ne bot
-- statement:
--   The card fiber le of ne bot construction uses the card fiber le of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L237-L241
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L237-L241

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

theorem card_fiber_le_of_ne_bot {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    Fintype.card (Fiber t) ≤ 2 ^ (3 * 2 ^ (Fintype.card α - 2)) := by sorry
