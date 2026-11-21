-- Prove2me | Theorems.Thm_Mpfx_Format_mem_toSet
-- name    : Mpfx.Format.mem_toSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:20.104026+00:00
-- url     : https://prove2.me/theorems/509993d4-041e-498e-a584-64e93b7aa58c
-- title:
--   Format: mem to Set
-- statement:
--   The Format construction uses the mem to Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L42-L43
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L42-L43

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.mem_toSet {F : Format} {x : Dyadic} :
    x ∈ F.toSet ↔ x ∈ F := by sorry
