-- Prove2me | Theorems.Thm_le_ex_permPattern
-- name    : le_ex_permPattern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:50.339203+00:00
-- url     : https://prove2.me/theorems/ce16bd83-c697-43fe-977d-fd412cb851ad
-- title:
--   le ex perm Pattern: le ex perm Pattern
-- statement:
--   The le ex perm Pattern construction uses the le ex perm Pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L941-L944
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L941-L944

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

theorem le_ex_permPattern (σ : Perm (Fin k)) (n : ℕ) (hk : 2 ≤ k) : n ≤ ex (PermPattern σ) n := by sorry
