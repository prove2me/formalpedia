-- Prove2me | Theorems.Thm_Mpfx_Format_next_zero
-- name    : Mpfx.Format.next_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:28.748992+00:00
-- url     : https://prove2.me/theorems/c104fd13-439b-4a14-b532-d1b1783c1817
-- title:
--   Format: next zero
-- statement:
--   With a minimum quantum, the successor of `0` is that quantum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L187-L191
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L187-L191

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.next_zero (F : Format) {e : ℤ} (he : F.exp = (e : QExp)) :
    F.next 0 = _root_.Mpfx.Dyadic.ofIntZpow 1 e := by sorry
