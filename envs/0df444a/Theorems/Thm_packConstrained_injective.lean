-- Prove2me | Theorems.Thm_packConstrained_injective
-- name    : packConstrained_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:44.855846+00:00
-- url     : https://prove2.me/theorems/128288ce-b6ec-41f3-a2d7-6c7b1b62ca5e
-- title:
--   pack Constrained injective: pack Constrained injective
-- statement:
--   The pack Constrained injective construction uses the pack Constrained injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L128-L150
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L128-L150

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

theorem packConstrained_injective (a b : α) (hne : a ≠ b) :
    Function.Injective (packConstrained a b hne) := by sorry
