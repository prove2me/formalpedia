-- Prove2me | Theorems.Thm_ex_perm_recurrence
-- name    : ex_perm_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:41.544376+00:00
-- url     : https://prove2.me/theorems/b8ce01e4-aecd-4b57-849e-3f034839f916
-- title:
--   ex perm recurrence: ex perm recurrence
-- statement:
--   The ex perm recurrence construction uses the ex perm recurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L657-L737
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L657-L737

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

theorem ex_perm_recurrence (σ : Perm (Fin k)) (n : ℕ) (hkn : k ^ 2 ∣ n) :
    ex (PermPattern σ) n
      ≤ (k - 1) ^ 2 * ex (PermPattern σ) (n / k ^ 2) + 2 * n * k ^ 3 * (k ^ 2).choose k := by sorry
