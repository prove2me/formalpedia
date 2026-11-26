-- Prove2me | Theorems.Thm_remainder_exp_add_n_le
-- name    : remainder_exp_add_n_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:17.930132+00:00
-- url     : https://prove2.me/theorems/fc6a6c12-ec3b-4038-8676-d0ec91d16202
-- title:
--   remainder exp add n le: remainder exp add n le
-- statement:
--   The remainder exp add n le construction uses the remainder exp add n le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L350-L368
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L350-L368

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
open Filter Topology

theorem remainder_exp_add_n_le (n : ℕ) (hn : 10 ≤ n) :
    n * (n - 1) + 3 * 2 ^ (n - 2) + n ≤ 2 ^ n - n := by sorry
