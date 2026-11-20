-- Prove2me | Theorems.Thm_density_def
-- name    : density_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:02:01.759856+00:00
-- url     : https://prove2.me/theorems/41202b5d-83da-40ae-985a-e1447ac4ad51
-- title:
--   density def: density def
-- statement:
--   The density def construction uses the density def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L22-L23
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/ExtremalFunction.lean#L22-L23

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

theorem density_def {n : ℕ} (M : Fin n → Fin n → Prop) [DecidableRel M] :
    density M = #{ij : Fin n × Fin n | M ij.1 ij.2} := by sorry
