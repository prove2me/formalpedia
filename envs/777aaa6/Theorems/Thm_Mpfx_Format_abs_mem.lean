-- Prove2me | Theorems.Thm_Mpfx_Format_abs_mem
-- name    : Mpfx.Format.abs_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:22.0223+00:00
-- url     : https://prove2.me/theorems/7bda5b65-d8f9-444b-919c-d23d747b1ca0
-- title:
--   Format: abs mem
-- statement:
--   `Dyadic.abs x ∈ F` whenever `x ∈ F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L155-L160
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L155-L160

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.abs_mem {F : Format} {x : Dyadic} (hx : x ∈ F) :
    Dyadic.abs x ∈ F := by sorry
