-- Prove2me | Theorems.Thm_Mpfx_Format_special_mem_opAdd_iff
-- name    : Mpfx.Format.special_mem_opAdd_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:10.010303+00:00
-- url     : https://prove2.me/theorems/96eb40ed-dd88-41ff-ad47-7d3008d801fd
-- title:
--   Format: special mem op Add iff
-- statement:
--   The specials of `opAdd` are exactly the special sums.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L438-L466
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L438-L466

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.special_mem_opAdd_iff {F₁ F₂ : Format} {s : Special} :
    s ∈ (opAdd F₁ F₂).specials ↔
      ∃ u ∈ F₁.values, ∃ v ∈ F₂.values, u + v = .special s := by sorry
