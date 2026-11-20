-- Prove2me | Theorems.Thm_density_mk_mem_product
-- name    : density_mk_mem_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:03:46.667627+00:00
-- url     : https://prove2.me/theorems/5dc6ead7-153c-4b29-8e98-d212aa17f3fe
-- title:
--   density mk mem product: density mk mem product
-- statement:
--   The density mk mem product construction uses the density mk mem product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L118-L119
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L118-L119

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

theorem density_mk_mem_product {n : ℕ} (I J : Finset (Fin n)) :
    density (fun i j ↦ (i, j) ∈ I ×ˢ J) = #I * #J := by sorry
