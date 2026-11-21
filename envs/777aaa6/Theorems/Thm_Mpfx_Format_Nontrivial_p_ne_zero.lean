-- Prove2me | Theorems.Thm_Mpfx_Format_Nontrivial_p_ne_zero
-- name    : Mpfx.Format.Nontrivial.p_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:01.934175+00:00
-- url     : https://prove2.me/theorems/11a51e44-bc4a-437b-9f24-498c2113bdea
-- title:
--   Nontrivial: p ne zero
-- statement:
--   A nonzero value needs at least one digit, so a nontrivial format has
--   positive precision.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L171-L176
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L171-L176

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.Nontrivial.p_ne_zero {F : Format} (h : F.Nontrivial) : F.p ≠ 0 := by sorry
