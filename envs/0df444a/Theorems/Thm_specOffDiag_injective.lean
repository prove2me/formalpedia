-- Prove2me | Theorems.Thm_specOffDiag_injective
-- name    : specOffDiag_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:50.983713+00:00
-- url     : https://prove2.me/theorems/726136a2-360a-5b67-8bbb-9743f07cffee
-- title:
--   spec Off Diag injective: spec Off Diag injective
-- statement:
--   The spec Off Diag injective construction uses the spec Off Diag injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L203-L212
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L203-L212

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

theorem specOffDiag_injective :
    Function.Injective (specOffDiag : TopologicalSpace α → Set {p : α × α // p.1 ≠ p.2}) := by sorry
