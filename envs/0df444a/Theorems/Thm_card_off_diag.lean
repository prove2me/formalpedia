-- Prove2me | Theorems.Thm_card_off_diag
-- name    : card_off_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:52.188797+00:00
-- url     : https://prove2.me/theorems/375f4642-5bce-4317-bb9e-8c91a0d916ff
-- title:
--   card off diag: card off diag
-- statement:
--   The card off diag construction uses the card off diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L214-L227
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L214-L227

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

theorem card_off_diag :
    Fintype.card {p : α × α // p.1 ≠ p.2} =
      Fintype.card α * (Fintype.card α - 1) := by sorry
