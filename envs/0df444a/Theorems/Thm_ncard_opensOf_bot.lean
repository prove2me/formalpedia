-- Prove2me | Theorems.Thm_ncard_opensOf_bot
-- name    : ncard_opensOf_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:12.295064+00:00
-- url     : https://prove2.me/theorems/606fee97-4e8e-454a-bde2-889b4558ee88
-- title:
--   ncard opens Of bot: ncard opens Of bot
-- statement:
--   The ncard opens Of bot construction uses the ncard opens Of bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L40-L42
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L40-L42

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

theorem ncard_opensOf_bot :
    ncard (opensOf (⊥ : TopologicalSpace α)) = 2 ^ Fintype.card α := by sorry
