-- Prove2me | Theorems.Thm_eq_of_constant_eq
-- name    : eq_of_constant_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:31.826398+00:00
-- url     : https://prove2.me/theorems/e0aa963d-b742-4fb2-9148-32b9d521a44f
-- title:
--   eq of constant eq: eq of constant eq
-- statement:
--   The output of equal constant functions with inhabited domain is equal.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L516-L518
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Basic.lean#L516-L518

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

theorem eq_of_constant_eq {α β} {c c' : β} [Inhabited α] :
    Function.const α c = Function.const α c' → c = c' := by sorry
