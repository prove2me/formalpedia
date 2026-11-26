-- Prove2me | Theorems.Thm_two_mul_pow
-- name    : two_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:04.525185+00:00
-- url     : https://prove2.me/theorems/67dec2db-de5a-4229-8570-d810c9d4c392
-- title:
--   two mul pow: two mul pow
-- statement:
--   The two mul pow construction uses the two mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L283-L284
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB/Asymptotics.lean#L283-L284

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

theorem two_mul_pow (a : ℕ) : 2 ^ a * 2 = 2 * 2 ^ a := by sorry
