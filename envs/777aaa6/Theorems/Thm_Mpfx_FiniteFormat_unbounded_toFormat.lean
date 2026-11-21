-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
-- name    : Mpfx.FiniteFormat.unbounded_toFormat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:36.875827+00:00
-- url     : https://prove2.me/theorems/ad82fb3d-3551-4880-a7dd-f0ea01fa594d
-- title:
--   Finite Format: unbounded to Format
-- statement:
--   The Finite Format construction uses the unbounded to Format property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L395-L396
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L395-L396

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.unbounded_toFormat (F : FiniteFormat) :
    F.unbounded.toFormat = F.toFormat.unbounded := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_toFormat
