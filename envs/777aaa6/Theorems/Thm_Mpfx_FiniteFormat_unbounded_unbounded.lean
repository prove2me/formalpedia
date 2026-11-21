-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
-- name    : Mpfx.FiniteFormat.unbounded_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:58.281262+00:00
-- url     : https://prove2.me/theorems/05e33286-98aa-4b62-a4cf-e7c0a073e1a1
-- title:
--   Finite Format: unbounded unbounded
-- statement:
--   The Finite Format construction uses the unbounded unbounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L402-L403
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L402-L403

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.unbounded_unbounded (F : FiniteFormat) :
    F.unbounded.unbounded = F.unbounded := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_unbounded
