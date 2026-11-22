-- Prove2me | Theorems.Thm_Fpy_toReal_abs
-- name    : Fpy.toReal_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:26.46239+00:00
-- url     : https://prove2.me/theorems/76b3d2b8-cecc-4b6c-9442-f02d24ef1a77
-- title:
--   Fpy: to Real abs
-- statement:
--   The Fpy construction uses the to Real abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L41-L43
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L41-L43

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.toReal_abs (u : WithSpecial Mpfx.Dyadic) :
    Num.abs u.toReal = (WithSpecial.abs u).toReal := by sorry
