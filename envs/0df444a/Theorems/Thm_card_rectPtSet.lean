-- Prove2me | Theorems.Thm_card_rectPtSet
-- name    : card_rectPtSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:00:46.580467+00:00
-- url     : https://prove2.me/theorems/aaf048c2-fa60-4c29-906f-876ff911ebe6
-- title:
--   card rect Pt Set: card rect Pt Set
-- statement:
--   The card rect Pt Set construction uses the card rect Pt Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L100-L105
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L100-L105

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

theorem card_rectPtSet (n a₁ b₁ a₂ b₂ : ℕ) (h : b₁ ≤ n ∧ b₂ ≤ n) :
    #(rectPtset n a₁ b₁ a₂ b₂) = (b₁ - a₁) * (b₂ - a₂) := by sorry
