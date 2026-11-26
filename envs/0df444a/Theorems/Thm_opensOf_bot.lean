-- Prove2me | Theorems.Thm_opensOf_bot
-- name    : opensOf_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:05.960495+00:00
-- url     : https://prove2.me/theorems/cf8a2475-b3d3-4334-970e-533d4b53343b
-- title:
--   opens Of bot: opens Of bot
-- statement:
--   The opens Of bot construction uses the opens Of bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L36-L38
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L36-L38

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

theorem opensOf_bot : opensOf (⊥ : TopologicalSpace α) = univ := by sorry
