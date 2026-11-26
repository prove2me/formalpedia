-- Prove2me | Theorems.Thm_two_pow_poly_le
-- name    : two_pow_poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:00.846319+00:00
-- url     : https://prove2.me/theorems/baccaf07-049e-50bb-a045-6615044fd08c
-- title:
--   two pow poly le: two pow poly le
-- statement:
--   The two pow poly le construction uses the two pow poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L297-L317
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L297-L317

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

theorem two_pow_poly_le (n : ℕ) (hn : 10 ≤ n) : n ^ 2 + n ≤ 2 ^ (n - 2) := by sorry
