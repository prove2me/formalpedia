-- Prove2me | Theorems.Thm_Mpfx_Format_special_mem_opAbs_iff
-- name    : Mpfx.Format.special_mem_opAbs_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:20.460701+00:00
-- url     : https://prove2.me/theorems/10145ea6-0fdd-45fc-b6f0-7c2721ff38f7
-- title:
--   Format: special mem op Abs iff
-- statement:
--   The specials of `opAbs` are exactly the absolute values of specials.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L495-L510
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L495-L510

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.special_mem_opAbs_iff {F : Format} {s : Special} :
    s ∈ (opAbs F).specials ↔ ∃ u ∈ F.values, WithSpecial.abs u = .special s := by sorry
