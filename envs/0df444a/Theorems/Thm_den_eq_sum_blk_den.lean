-- Prove2me | Theorems.Thm_den_eq_sum_blk_den
-- name    : den_eq_sum_blk_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:21.5548+00:00
-- url     : https://prove2.me/theorems/d5f06181-b371-43cd-8d43-6dc91e868391
-- title:
--   den eq sum blk den: den eq sum blk den
-- statement:
--   The den eq sum blk den construction uses the den eq sum blk den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L154-L188
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L154-L188

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
open scoped Classical

theorem den_eq_sum_blk_den (M : Fin n → Fin n → Prop) (hqn : q ∣ n) :
    let B := blkMatrix M q
    density M = ∑ ij : Fin (n / q) × Fin (n / q) with B ij.1 ij.2, blk_den M ij.1 ij.2 := by sorry
