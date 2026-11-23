-- Prove2me | Theorems.Thm_not_OEdge_of_isTerminal
-- name    : not_OEdge_of_isTerminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:35.244315+00:00
-- url     : https://prove2.me/theorems/49d07ceb-9d68-412e-9cf2-d62de38d05cb
-- title:
--   not OEdge of is Terminal: not OEdge of is Terminal
-- statement:
--   The not OEdge of is Terminal construction uses the not OEdge of is Terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L555-L558
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L555-L558

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

theorem not_OEdge_of_isTerminal {O : OBdd n m}: O.isTerminal → ¬ OEdge O U := by sorry
