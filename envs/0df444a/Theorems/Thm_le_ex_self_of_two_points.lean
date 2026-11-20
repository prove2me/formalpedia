-- Prove2me | Theorems.Thm_le_ex_self_of_two_points
-- name    : le_ex_self_of_two_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:04:59.546173+00:00
-- url     : https://prove2.me/theorems/0bafad63-931f-4eda-b2da-2f2e407bfd3d
-- title:
--   le ex self of two points: le ex self of two points
-- statement:
--   The le ex self of two points construction uses the le ex self of two points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L185-L196
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L185-L196

module
public import Definitions.Def_ScoutForbiddenMatrixContainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ] {m n : ℕ}
  {P : α → β → Prop}

theorem le_ex_self_of_two_points (P : α → β → Prop) (n : ℕ)
    (hP : ∃ x y : (α × β), P x.1 x.2 ∧ P y.1 y.2 ∧ x ≠ y) : n ≤ ex P n := by sorry
