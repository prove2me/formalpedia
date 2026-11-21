-- Prove2me | Theorems.Thm_Mpfx_Format_Nontrivial_exists_sign
-- name    : Mpfx.Format.Nontrivial.exists_sign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:47.028965+00:00
-- url     : https://prove2.me/theorems/f391b28f-b4c8-4107-8c1a-7fc57a9c7943
-- title:
--   Nontrivial: exists sign
-- statement:
--   A nontrivial format has a nonzero value of either sign: a positive value
--   or its negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L197-L206
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L197-L206

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.Nontrivial.exists_sign {F : Format} (h : F.Nontrivial) (b : Bool) :
    ∃ y : Dyadic, y ∈ F ∧ y ≠ 0 ∧ decide ((y : ℚ) < 0) = b := by sorry
