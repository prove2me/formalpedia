-- Prove2me | Theorems.Thm_Fpy_toReal_mul
-- name    : Fpy.toReal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:11:44.609888+00:00
-- url     : https://prove2.me/theorems/5e4418d2-33e5-4ee7-a3e2-3abeaeed5e20
-- title:
--   Fpy: to Real mul
-- statement:
--   The Fpy construction uses the to Real mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L29-L36
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L29-L36

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.toReal_mul (u v : WithSpecial Mpfx.Dyadic) :
    Num.mul u.toReal v.toReal = (u * v).toReal := by sorry
