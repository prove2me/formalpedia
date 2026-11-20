-- Prove2me | Theorems.Thm_permPattern_refl
-- name    : permPattern_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:18.563705+00:00
-- url     : https://prove2.me/theorems/38963cde-e4ad-4119-bea5-8ad939fcf91d
-- title:
--   perm Pattern refl: perm Pattern refl
-- statement:
--   The perm Pattern refl construction uses the perm Pattern refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L27-L28
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L27-L28

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

theorem permPattern_refl (n : ℕ) :
    PermPattern (.refl _ : Equiv.Perm (Fin n)) = IdentityPattern n := by sorry

attribute [defeq] permPattern_refl
