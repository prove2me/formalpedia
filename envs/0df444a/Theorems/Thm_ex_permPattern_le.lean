-- Prove2me | Theorems.Thm_ex_permPattern_le
-- name    : ex_permPattern_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:44.678616+00:00
-- url     : https://prove2.me/theorems/87b7df1b-2971-4f18-ba8d-5c844798a0f5
-- title:
--   ex perm Pattern le: ex perm Pattern le
-- statement:
--   The ex perm Pattern le construction uses the ex perm Pattern le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L848-L939
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L848-L939

module
public import Definitions.Def_ForbiddenMatrix_SmallPatterns
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Nat.Choose.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Qify
public import Definitions.Def_ForbiddenMatrix_PermutationPatterns
set_option autoImplicit true
@[expose] public section
public section
open Finset Set OrderDual Equiv
variable {k n q : ℕ}

theorem ex_permPattern_le (σ : Perm (Fin k)) (n : ℕ) :
    ex (PermPattern σ) n ≤ 2 * k ^ 4 * (k ^ 2).choose k * n := by sorry
