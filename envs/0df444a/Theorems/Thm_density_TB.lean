-- Prove2me | Theorems.Thm_density_TB
-- name    : density_TB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:24.423198+00:00
-- url     : https://prove2.me/theorems/72c6a5f2-faa9-4679-9d54-c0181e233977
-- title:
--   density TB: density TB
-- statement:
--   The density TB construction uses the density TB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L486-L601
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L486-L601

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

theorem density_TB {n k : ℕ} (h_n : 0 < n) (h_k : k ^ 2 ∣ n) (M : Fin n → Fin n → Prop)
    {σ : Perm (Fin k)} (M_avoid_perm : ¬ Contains (PermPattern σ) M) :
    let q := k ^ 2
    let B := blkMatrix M q
    let T (i j : Fin (n / q)) : Prop := k ≤ #{r | ∃ c, (r, c) ∈ rectPtsetqMatrix M q i j}
    let TB : Fin (n / q) → Fin (n / q) → Prop := fun i j ↦ T i j ∧ B i j
    density TB ≤ n / k ^ 2 * (k * (k ^ 2).choose k) := by sorry
