-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
-- name    : Mpfx.FiniteFormat.unbounded_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:45.881747+00:00
-- url     : https://prove2.me/theorems/0b0d7e19-52c0-4fb3-a4aa-2c40f8ed990a
-- title:
--   Finite Format: unbounded exp
-- statement:
--   The Finite Format construction uses the unbounded exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L400-L400
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L400-L400

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.unbounded_exp (F : FiniteFormat) : F.unbounded.exp = F.exp := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_exp
