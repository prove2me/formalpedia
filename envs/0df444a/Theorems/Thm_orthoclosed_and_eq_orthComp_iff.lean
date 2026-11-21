-- Prove2me | Theorems.Thm_orthoclosed_and_eq_orthComp_iff
-- name    : orthoclosed_and_eq_orthComp_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:23.000917+00:00
-- url     : https://prove2.me/theorems/df1b8526-c862-41d0-9d54-bbf2a64cbf50
-- title:
--   orthoclosed and eq orth Comp iff: orthoclosed and eq orth Comp iff
-- statement:
--   Characterization of orthocomplements:
--       X is orthoclosed and Y = X⊥ if and only if
--       (1) X ⊥ Y (every element of X is orthogonal to every element of Y), and
--       (2) every z ∉ X ∪ Y is non-orthogonal to some element of X and
--           non-orthogonal to some element of Y.
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L53-L107
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L53-L107

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]

theorem orthoclosed_and_eq_orthComp_iff (X Y : Set O) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, (∃ x ∈ X, ¬ z ⊥ x) ∧ (∃ y ∈ Y, ¬ z ⊥ y))) := by sorry
