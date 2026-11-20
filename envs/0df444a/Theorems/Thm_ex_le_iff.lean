-- Prove2me | Theorems.Thm_ex_le_iff
-- name    : ex_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:04:57.303193+00:00
-- url     : https://prove2.me/theorems/e17944c9-1ef0-4c7b-981c-07948a28c442
-- title:
--   ex le iff: ex le iff
-- statement:
--   The ex le iff construction uses the ex le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L39-L41
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L39-L41

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

theorem ex_le_iff {P : α → β → Prop} {m n : ℕ} :
    ex P n ≤ m ↔ ∀ (M : Fin n → Fin n → Prop), ¬ Contains P M → density M ≤ m:= by sorry
