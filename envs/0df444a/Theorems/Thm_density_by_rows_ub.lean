-- Prove2me | Theorems.Thm_density_by_rows_ub
-- name    : density_by_rows_ub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:18.108269+00:00
-- url     : https://prove2.me/theorems/59c3838b-8a9c-4d9a-91ba-0c44468d234b
-- title:
--   density by rows ub: density by rows ub
-- statement:
--   The density by rows ub construction uses the density by rows ub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L63-L68
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L63-L68

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

theorem density_by_rows_ub {n c : ℕ} (M : Fin n → Fin n → Prop)
    (h_row_density_bounded : ∀ i, row_density M i ≤ c) : density M ≤ n * c := by sorry
