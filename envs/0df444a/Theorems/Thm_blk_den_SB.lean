-- Prove2me | Theorems.Thm_blk_den_SB
-- name    : blk_den_SB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:32.348794+00:00
-- url     : https://prove2.me/theorems/ccedb8b2-3959-4d3a-b14f-d252824cfecb
-- title:
--   blk den SB: blk den SB
-- statement:
--   The blk den SB construction uses the blk den SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L604-L636
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L604-L636

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
set_option backward.isDefEq.respectTransparency false

theorem blk_den_SB {n : ℕ} (k : ℕ) (M : Fin n → Fin n → Prop) :
    let q := k ^ 2
    let B := blkMatrix M q
    let W (i j : Fin (n / q)) : Prop := k ≤ #{c | ∃ r, (r, c) ∈ rectPtsetqMatrix M q i j}
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let S : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ ¬ W i j ∧ ¬ T i j
    let SB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ S i j ∧ B i j
    ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k - 1) ^ 2 := by sorry
