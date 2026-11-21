-- Prove2me | Theorems.Thm_Mpfx_Format_zero_mem
-- name    : Mpfx.Format.zero_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:24:57.248091+00:00
-- url     : https://prove2.me/theorems/0b976f29-de95-412a-b2c6-7bb9996352ac
-- title:
--   Format: zero mem
-- statement:
--   Zero is in every format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L231-L241
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L231-L241

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.zero_mem (F : Format) : (0 : Dyadic) ∈ F := by sorry
