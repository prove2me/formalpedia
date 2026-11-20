-- Prove2me | Theorems.Thm_split_density_to_rows
-- name    : split_density_to_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:38.454179+00:00
-- url     : https://prove2.me/theorems/74c5e11a-1d98-48b2-a210-1bfecf2096b6
-- title:
--   split density to rows: split density to rows
-- statement:
--   The split density to rows construction uses the split density to rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L58-L61
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L58-L61

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

theorem split_density_to_rows {n : ℕ} (M : Fin n → Fin n → Prop) :
    density M = ∑ i, row_density M i := by sorry
