-- Prove2me | Theorems.Thm_isOpen_bot
-- name    : isOpen_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:44:49.148837+00:00
-- url     : https://prove2.me/theorems/e6183e40-cb85-4a50-94c8-4b1b20669ed4
-- title:
--   is Open bot: is Open bot
-- statement:
--   The is Open bot construction uses the is Open bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L34-L34
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L34-L34

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

theorem isOpen_bot (U : Set α) : @IsOpen α ⊥ U := by sorry
