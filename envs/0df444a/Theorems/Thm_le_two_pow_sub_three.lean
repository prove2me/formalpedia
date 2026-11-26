-- Prove2me | Theorems.Thm_le_two_pow_sub_three
-- name    : le_two_pow_sub_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:07.515848+00:00
-- url     : https://prove2.me/theorems/dd519080-2be7-57fb-a14c-0e82937021f2
-- title:
--   le two pow sub three: le two pow sub three
-- statement:
--   The le two pow sub three construction uses the le two pow sub three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L286-L295
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L286-L295

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

theorem le_two_pow_sub_three (k : ℕ) (hk : 10 ≤ k) : k + 1 ≤ 2 ^ (k - 3) := by sorry
