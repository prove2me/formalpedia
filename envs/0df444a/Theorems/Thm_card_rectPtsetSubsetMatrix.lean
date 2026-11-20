-- Prove2me | Theorems.Thm_card_rectPtsetSubsetMatrix
-- name    : card_rectPtsetSubsetMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:01:06.307265+00:00
-- url     : https://prove2.me/theorems/9157bfc0-5ad1-463c-a2c4-5f1fdf04ce81
-- title:
--   card rect Ptset Subset Matrix: card rect Ptset Subset Matrix
-- statement:
--   The card rect Ptset Subset Matrix construction uses the card rect Ptset Subset Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L107-L116
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L107-L116

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

theorem card_rectPtsetSubsetMatrix {n : ℕ} (M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) :
    #(rectPtsetSubsetMatrix M R C) ≤ #R * #C := by sorry
