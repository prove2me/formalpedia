-- Prove2me | Theorems.Thm_split_density_blk
-- name    : split_density_blk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:27.706802+00:00
-- url     : https://prove2.me/theorems/c69089d0-c97e-4a5c-8446-404fce97d44b
-- title:
--   split density blk: split density blk
-- statement:
--   The split density blk construction uses the split density blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L270-L325
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L270-L325

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

theorem split_density_blk {n q : ℕ} (hqn : q ∣ n) (M : Fin n → Fin n → Prop)
    (f1 f2 : Fin (n / q) → Fin (n / q) → Prop) :
    let Q := Fin (n / q) × Fin (n / q)
    let f3 := fun i j ↦ (¬ f1 i j) ∧ ¬ (f2 i j)
    let B := blkMatrix M q
    let B1 (i j : Fin (n / q)) : Prop := B i j ∧ f1 i j
    let B2 (i j : Fin (n / q)) : Prop := B i j ∧ f2 i j
    let N  (i j : Fin (n / q)) : Prop := B i j ∧ f3 i j
    density M ≤ ∑ ij : Q with B1 ij.1 ij.2, blk_den M ij.1 ij.2 +
                ∑ ij : Q with B2 ij.1 ij.2, blk_den M ij.1 ij.2 +
                ∑ ij : Q with N ij.1 ij.2, blk_den M ij.1 ij.2 := by sorry
