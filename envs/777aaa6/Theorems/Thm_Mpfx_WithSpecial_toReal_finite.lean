-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_toReal_finite
-- name    : Mpfx.WithSpecial.toReal_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:29.14134+00:00
-- url     : https://prove2.me/theorems/2da5c380-52d9-42b0-a5ed-88ee4c044231
-- title:
--   With Special: to Real finite
-- statement:
--   The With Special construction uses the to Real finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L54-L55
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L54-L55

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.WithSpecial.toReal_finite (d : Dyadic) :
    (WithSpecial.finite d).toReal = .finite (d : ℝ) := by sorry

attribute [defeq] Mpfx.WithSpecial.toReal_finite
