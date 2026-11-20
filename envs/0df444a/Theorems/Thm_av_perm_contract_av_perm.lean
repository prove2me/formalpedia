-- Prove2me | Theorems.Thm_av_perm_contract_av_perm
-- name    : av_perm_contract_av_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:24.912508+00:00
-- url     : https://prove2.me/theorems/50073d1c-5206-4cb0-b6cf-96c32f1c075a
-- title:
--   av perm contract av perm: av perm contract av perm
-- statement:
--   The av perm contract av perm construction uses the av perm contract av perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L338-L367
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L338-L367

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

theorem av_perm_contract_av_perm (q : ℕ) (σ : Perm (Fin k)) (M : Fin n → Fin n → Prop)
    (hM : ¬ Contains (PermPattern σ) M) : ¬ Contains (PermPattern σ) (blkMatrix M q) := by sorry
