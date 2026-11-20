-- Prove2me | Theorems.Thm_ex_vertical
-- name    : ex_vertical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:09:59.452031+00:00
-- url     : https://prove2.me/theorems/b2d0ea37-5722-40c5-825c-6640ae8e1b94
-- title:
--   ex vertical: ex vertical
-- statement:
--   The ex vertical construction uses the ex vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L234-L259
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L234-L259

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

theorem ex_vertical (k n : ℕ) : ex (VerticalPattern k) n ≤ n*(k-1) := by sorry
