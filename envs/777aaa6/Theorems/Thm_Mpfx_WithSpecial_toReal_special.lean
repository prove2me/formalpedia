-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_toReal_special
-- name    : Mpfx.WithSpecial.toReal_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:36.723127+00:00
-- url     : https://prove2.me/theorems/c890b6f4-c359-49e9-8ea4-56cec9254a8e
-- title:
--   With Special: to Real special
-- statement:
--   The With Special construction uses the to Real special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L57-L58
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L57-L58

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.WithSpecial.toReal_special (s : Special) :
    (WithSpecial.special s : WithSpecial Dyadic).toReal = .special s := by sorry

attribute [defeq] Mpfx.WithSpecial.toReal_special
