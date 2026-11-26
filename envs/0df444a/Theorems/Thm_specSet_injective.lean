-- Prove2me | Theorems.Thm_specSet_injective
-- name    : specSet_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:56.767607+00:00
-- url     : https://prove2.me/theorems/b069ca67-12f1-406c-93b1-c435f949fdf9
-- title:
--   spec Set injective: spec Set injective
-- statement:
--   The spec Set injective construction uses the spec Set injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L184-L197
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L184-L197

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
omit [DecidableEq α]

theorem specSet_injective :
    Function.Injective (specSet : TopologicalSpace α → Set (α × α)) := by sorry
