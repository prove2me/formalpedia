-- Prove2me | Theorems.Thm_le_ex_iff
-- name    : le_ex_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:11.295407+00:00
-- url     : https://prove2.me/theorems/57231c0f-a6db-45b4-99b0-d96556477ba1
-- title:
--   le ex iff: le ex iff
-- statement:
--   The le ex iff construction uses the le ex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L43-L47
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L43-L47

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

theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b) {m n : ℕ} :
    m ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop), ¬ Contains P M ∧ m ≤ density M := by sorry
