-- Prove2me | Theorems.Thm_Mpfx_Format_special_mem_values
-- name    : Mpfx.Format.special_mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:17.708609+00:00
-- url     : https://prove2.me/theorems/d17388ba-4682-4b07-acc3-46292bcfbb61
-- title:
--   Format: special mem values
-- statement:
--   The Format construction uses the special mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L118-L119
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L118-L119

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.Format.special_mem_values {F : Format} {s : Special} :
    WithSpecial.special s ∈ F.values ↔ s ∈ F.specials := by sorry
