-- Prove2me | Theorems.Thm_Mpfx_Format_withBound_exp
-- name    : Mpfx.Format.withBound_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:39:33.06108+00:00
-- url     : https://prove2.me/theorems/14719b79-ef46-44ab-8e13-a953624e1131
-- title:
--   Format: with Bound exp
-- statement:
--   The Format construction uses the with Bound exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L27-L28
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L27-L28

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.withBound_exp (F : Format) (b' : Bound) :
    (F.withBound b').exp = F.exp := by sorry

attribute [defeq] Mpfx.Format.withBound_exp
