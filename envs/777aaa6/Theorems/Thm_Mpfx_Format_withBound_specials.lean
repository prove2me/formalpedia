-- Prove2me | Theorems.Thm_Mpfx_Format_withBound_specials
-- name    : Mpfx.Format.withBound_specials
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:37.112718+00:00
-- url     : https://prove2.me/theorems/b6c43310-9432-4256-a597-1a44e555fcf1
-- title:
--   Format: with Bound specials
-- statement:
--   The Format construction uses the with Bound specials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L32-L33
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L32-L33

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.withBound_specials (F : Format) (b' : Bound) :
    (F.withBound b').specials = F.specials := by sorry

attribute [defeq] Mpfx.Format.withBound_specials
