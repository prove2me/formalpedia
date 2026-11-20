-- Prove2me | Theorems.Thm_den_submatrix_eq_sum_blk_den
-- name    : den_submatrix_eq_sum_blk_den
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:21.409302+00:00
-- url     : https://prove2.me/theorems/00cbb886-220f-42d4-bb44-fd278a9548cb
-- title:
--   den submatrix eq sum blk den: den submatrix eq sum blk den
-- statement:
--   The den submatrix eq sum blk den construction uses the den submatrix eq sum blk den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L210-L267
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L210-L267

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

theorem den_submatrix_eq_sum_blk_den (M : Fin n → Fin n → Prop)
    (hqn : q ∣ n) (f1 : Fin (n / q) → Fin (n / q) → Prop) :
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let fq (x : Fin n) : Fin (n / q) := ⟨x / q, Nat.div_lt_div_of_lt_of_dvd hqn x.isLt⟩
    let M1 (i j : Fin n) : Prop := M i j ∧ B1 (fq i) (fq j);
    let Q := Fin (n / q) × Fin (n / q)
    density M1 = ∑ ij : Q with B1 ij.1 ij.2, blk_den M ij.1 ij.2 := by sorry
