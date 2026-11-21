-- Prove2me | Theorems.Thm_Mpfx_Format_bound_mem
-- name    : Mpfx.Format.bound_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:22.443527+00:00
-- url     : https://prove2.me/theorems/888ff96c-485f-4aad-9d4f-ea35c5a498cf
-- title:
--   Format: bound mem
-- statement:
--   A `BoundRep` format's finite bound is one of its values.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L222-L228
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L222-L228

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.bound_mem {F : Format} (hb : BoundRep F) {bv : NonNegDyadic}
    (hF : F.b = (bv : Bound)) : bv.val ∈ F := by sorry
