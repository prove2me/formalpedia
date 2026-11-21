-- Prove2me | Theorems.Thm_updown
-- name    : updown
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:55.589172+00:00
-- url     : https://prove2.me/theorems/ded13a80-4567-422b-8d39-d2abe9e80dd6
-- title:
--   updown: updown
-- statement:
--   Refinement of orthocomplements for the incomparability orthoset of a poset.
--       X is orthoclosed and Y = X⊥ iff X ⊥ Y and for every z ∉ X ∪ Y there exist
--       x ∈ X, y ∈ Y such that z < x and z < y (z below both), or x < z and y < z
--       (z above both).
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L166-L200
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L166-L200

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem updown (X Y : Set P) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, ∃ x ∈ X, ∃ y ∈ Y, (z < x ∧ z < y) ∨ (x < z ∧ y < z))) := by sorry
