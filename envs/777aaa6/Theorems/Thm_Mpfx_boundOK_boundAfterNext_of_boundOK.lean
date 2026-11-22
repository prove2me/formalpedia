-- Prove2me | Theorems.Thm_Mpfx_boundOK_boundAfterNext_of_boundOK
-- name    : Mpfx.boundOK_boundAfterNext_of_boundOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:28:05.876183+00:00
-- url     : https://prove2.me/theorems/b8b07c11-5d5a-4cec-8d98-81f0b03d5dd7
-- title:
--   Mpfx: bound OK bound After Next of bound OK
-- statement:
--   The relaxed bound `boundAfterNext` accepts anything the original bound
--   accepts (`b₁ ≤ next(b₁)`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L526-L541
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L526-L541

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.boundOK_boundAfterNext_of_boundOK {F₁ : FiniteFormat} {d : _root_.Mpfx.Dyadic}
    (hd_b : Format.boundOK F₁.b d) :
    Format.boundOK F₁.toFormat.boundAfterNext d := by sorry
