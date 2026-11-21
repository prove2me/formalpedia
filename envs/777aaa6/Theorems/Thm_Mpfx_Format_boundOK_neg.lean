-- Prove2me | Theorems.Thm_Mpfx_Format_boundOK_neg
-- name    : Mpfx.Format.boundOK_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:58.835855+00:00
-- url     : https://prove2.me/theorems/f8b37c65-6378-489a-ad15-926d7e5b802e
-- title:
--   Format: bound OK neg
-- statement:
--   The bound `|·| ≤ b` is symmetric under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L133-L140
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L133-L140

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.boundOK_neg {b : Bound} {d : Dyadic} (h : boundOK b d) :
    boundOK b (-d) := by sorry
