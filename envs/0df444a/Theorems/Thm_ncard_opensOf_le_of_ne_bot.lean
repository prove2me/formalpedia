-- Prove2me | Theorems.Thm_ncard_opensOf_le_of_ne_bot
-- name    : ncard_opensOf_le_of_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:47.971622+00:00
-- url     : https://prove2.me/theorems/40eeae76-c3fa-4842-9537-7591d4022fa3
-- title:
--   ncard opens Of le of ne bot: ncard opens Of le of ne bot
-- statement:
--   The ncard opens Of le of ne bot construction uses the ncard opens Of le of ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L175-L178
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L175-L178

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

theorem ncard_opensOf_le_of_ne_bot {t : TopologicalSpace α} (ht : t ≠ ⊥) :
    ncard (opensOf t) ≤ 3 * 2 ^ (Fintype.card α - 2) := by sorry
