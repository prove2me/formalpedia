-- Prove2me | Theorems.Thm_Mpfx_Format_special_mem_opMul_iff
-- name    : Mpfx.Format.special_mem_opMul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:03.479189+00:00
-- url     : https://prove2.me/theorems/538b3c85-df05-4070-aa27-77836dec844a
-- title:
--   Format: special mem op Mul iff
-- statement:
--   The specials of `opMul` are exactly the special products.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L391-L423
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L391-L423

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.special_mem_opMul_iff {F₁ F₂ : Format} {s : Special} :
    s ∈ (opMul F₁ F₂).specials ↔
      ∃ u ∈ F₁.values, ∃ v ∈ F₂.values, u * v = .special s := by sorry
