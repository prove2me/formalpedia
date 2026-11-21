-- Prove2me | Theorems.Thm_Mpfx_Format_unbounded_unbounded
-- name    : Mpfx.Format.unbounded_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:55.604175+00:00
-- url     : https://prove2.me/theorems/a4bdfb2d-c866-485e-b1d7-0d10d742ad8d
-- title:
--   Format: unbounded unbounded
-- statement:
--   The Format construction uses the unbounded unbounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L102-L103
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L102-L103

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.unbounded_unbounded (F : Format) :
    F.unbounded.unbounded = F.unbounded := by sorry

attribute [defeq] Mpfx.Format.unbounded_unbounded
