-- Prove2me | Theorems.Thm_Fpy_toReal_add
-- name    : Fpy.toReal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:11:50.517958+00:00
-- url     : https://prove2.me/theorems/11cbfb89-9166-49b3-989a-affb33548621
-- title:
--   Fpy: to Real add
-- statement:
--   The Fpy construction uses the to Real add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L24-L27
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L24-L27

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.toReal_add (u v : WithSpecial Mpfx.Dyadic) :
    Num.add u.toReal v.toReal = (u + v).toReal := by sorry
