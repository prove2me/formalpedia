-- Prove2me | Theorems.Thm_Mpfx_Format_withBound_b
-- name    : Mpfx.Format.withBound_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:37.49322+00:00
-- url     : https://prove2.me/theorems/16ce1564-a2b9-4daf-bb5e-3f034d09f570
-- title:
--   Format: with Bound b
-- statement:
--   The Format construction uses the with Bound b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L30-L31
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L30-L31

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.withBound_b (F : Format) (b' : Bound) :
    (F.withBound b').b = b' := by sorry

attribute [defeq] Mpfx.Format.withBound_b
