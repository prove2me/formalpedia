-- Prove2me | Theorems.Thm_sum_pos_iff_exists_pos
-- name    : sum_pos_iff_exists_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:39:37.670359+00:00
-- url     : https://prove2.me/theorems/c5c956bf-8f96-4afe-a8f4-f8796935f779
-- title:
--   sum pos iff exists pos: sum pos iff exists pos
-- statement:
--   A vector of natural numbers has positive sum iff at least one component is positive.
--
--   Source: https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Utils.lean#L35-L46
-- source:
--   https://github.com/mdbrnowski/apportionmentlib/blob/86d9058ae46a2c19c024cdd80e0bb14dbde9b562/Apportionmentlib/Utils.lean#L35-L46

module
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
public import Definitions.Def_Apportionmentlib_Utils
set_option autoImplicit false
@[expose] public section
public section

theorem sum_pos_iff_exists_pos {n : ℕ} {v : Vector ℕ n} : 0 < v.sum ↔ ∃ i : Fin n, 0 < v[i] := by sorry
