-- Prove2me | Theorems.Thm_ex_identityPattern_le
-- name    : ex_identityPattern_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:43.030834+00:00
-- url     : https://prove2.me/theorems/484616ff-713e-485b-af18-6582257f6832
-- title:
--   ex identity Pattern le: ex identity Pattern le
-- statement:
--   The ex identity Pattern le construction uses the ex identity Pattern le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L32-L73
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L32-L73

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

theorem ex_identityPattern_le (k n : ℕ) : ex (IdentityPattern k) n ≤ (2 * n - 1) * (k - 1) := by sorry
