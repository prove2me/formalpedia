-- Prove2me | Theorems.Thm_ex_horizontal
-- name    : ex_horizontal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:09:57.190944+00:00
-- url     : https://prove2.me/theorems/94871ce2-fabb-4535-840d-75f1a2183725
-- title:
--   ex horizontal: ex horizontal
-- statement:
--   The ex horizontal construction uses the ex horizontal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L218-L232
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L218-L232

module
public import Definitions.Def_ForbiddenMatrix_ExtremalFunction
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_ForbiddenMatrix_MatrixOperations
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
set_option autoImplicit true
@[expose] public section
public section
open Finset Set
variable {α β : Type*} [LinearOrder α] [LinearOrder β]

theorem ex_horizontal (k n : ℕ) : ex (HorizontalPattern k) n ≤ n*(k-1) := by sorry
