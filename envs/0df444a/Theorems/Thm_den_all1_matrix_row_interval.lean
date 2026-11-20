-- Prove2me | Theorems.Thm_den_all1_matrix_row_interval
-- name    : den_all1_matrix_row_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:04:47.785962+00:00
-- url     : https://prove2.me/theorems/bc97d095-377d-4127-8d24-dc6420cb0587
-- title:
--   den all1 matrix row interval: den all1 matrix row interval
-- statement:
--   The den all1 matrix row interval construction uses the den all1 matrix row interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L149-L161
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L149-L161

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

theorem den_all1_matrix_row_interval {n : ℕ} (a b : Fin n) :
    let I := ({x | ↑x ∈ Finset.Icc a.1 b.1} : Finset (Fin n))
    let M (i j : Fin n) : Prop := (i, j) ∈ I ×ˢ Finset.univ
    density M = n * (b + 1 - a) := by sorry
