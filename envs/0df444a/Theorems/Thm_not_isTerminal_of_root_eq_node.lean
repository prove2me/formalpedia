-- Prove2me | Theorems.Thm_not_isTerminal_of_root_eq_node
-- name    : not_isTerminal_of_root_eq_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:23.749858+00:00
-- url     : https://prove2.me/theorems/d7b66092-c6f0-4dd1-874c-28af0bc897ad
-- title:
--   not is Terminal of root eq node: not is Terminal of root eq node
-- statement:
--   The not is Terminal of root eq node construction uses the not is Terminal of root eq node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1017-L1020
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L1017-L1020

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered

theorem not_isTerminal_of_root_eq_node {n m} {j} {O : OBdd n m} (h : O.1.root = node j) : ¬ O.isTerminal := by sorry
