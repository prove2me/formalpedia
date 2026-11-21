-- Prove2me | Theorems.Thm_Mpfx_Format_boundAfterNext_top
-- name    : Mpfx.Format.boundAfterNext_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:32.047687+00:00
-- url     : https://prove2.me/theorems/7977737e-36b7-4d00-9c0c-67e48cf9cdc4
-- title:
--   Format: bound After Next top
-- statement:
--   `boundAfterNext` evaluator: `⊤` case.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L208-L209
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L208-L209

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.boundAfterNext_top {F : Format} (hF : F.b = ⊤) :
    F.boundAfterNext = ⊤ := by sorry
