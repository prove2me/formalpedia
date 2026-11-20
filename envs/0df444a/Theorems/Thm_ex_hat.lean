-- Prove2me | Theorems.Thm_ex_hat
-- name    : ex_hat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:02.261802+00:00
-- url     : https://prove2.me/theorems/b49f010b-8f82-4367-9979-42d67ecc79c8
-- title:
--   ex hat: ex hat
-- statement:
--   The ex hat construction uses the ex hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L262-L311
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/SmallPatterns.lean#L262-L311

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

theorem ex_hat (n : ℕ) : ex HatPattern n ≤ 3 * n := by sorry
