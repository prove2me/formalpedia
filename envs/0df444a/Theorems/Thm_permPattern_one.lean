-- Prove2me | Theorems.Thm_permPattern_one
-- name    : permPattern_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:10:25.726603+00:00
-- url     : https://prove2.me/theorems/43376bbb-9f8e-4b45-8afd-3333fa8a54f3
-- title:
--   perm Pattern one: perm Pattern one
-- statement:
--   The perm Pattern one construction uses the perm Pattern one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L24-L25
-- source:
--   https://github.com/YaelDillies/forbidden-matrix/blob/b2687f196ca1542408cd2d2460013f084bfda3df/ForbiddenMatrix/PermutationPatterns.lean#L24-L25

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

theorem permPattern_one (n : ℕ) :
    PermPattern (1 : Equiv.Perm (Fin n)) = IdentityPattern n := by sorry

attribute [defeq] permPattern_one
