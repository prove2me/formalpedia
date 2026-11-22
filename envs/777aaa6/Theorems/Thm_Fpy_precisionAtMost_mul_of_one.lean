-- Prove2me | Theorems.Thm_Fpy_precisionAtMost_mul_of_one
-- name    : Fpy.precisionAtMost_mul_of_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:09.295557+00:00
-- url     : https://prove2.me/theorems/05ae4c70-2d13-4307-a311-67b7a15a0789
-- title:
--   Fpy: precision At Most mul of one
-- statement:
--   The Fpy construction uses the precision At Most mul of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L99-L116
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L99-L116

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.precisionAtMost_mul_of_one {q : Prec} {x y : Mpfx.Dyadic}
    (hx : Dyadic.precisionAtMost ((1 : ℕ) : Prec) x) (hy : Dyadic.precisionAtMost q y) :
    Dyadic.precisionAtMost q (x * y) := by sorry
