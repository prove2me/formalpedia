-- Prove2me | Theorems.Thm_card_interval
-- name    : card_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:52.829177+00:00
-- url     : https://prove2.me/theorems/f1491d06-cee9-42dd-b65a-de1e288d2b51
-- title:
--   card interval: card interval
-- statement:
--   The card interval construction uses the card interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L93-L98
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L93-L98

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

theorem card_interval {n : ℕ} (x y : ℕ) (hy : y ≤ n) :
    #{a : Fin n | ↑a ∈ Finset.Ico x y} = #(.Ico x y) := by sorry
