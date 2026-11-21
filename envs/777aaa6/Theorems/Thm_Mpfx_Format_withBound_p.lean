-- Prove2me | Theorems.Thm_Mpfx_Format_withBound_p
-- name    : Mpfx.Format.withBound_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:29.509299+00:00
-- url     : https://prove2.me/theorems/c7d90858-6a82-4ff2-90f3-633c41eabacd
-- title:
--   Format: with Bound p
-- statement:
--   The Format construction uses the with Bound p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L24-L25
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L24-L25

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.withBound_p (F : Format) (b' : Bound) :
    (F.withBound b').p = F.p := by sorry

attribute [defeq] Mpfx.Format.withBound_p
