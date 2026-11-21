-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_format_next_eq
-- name    : Mpfx.FiniteFormat.format_next_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:51.659182+00:00
-- url     : https://prove2.me/theorems/09e31a0b-a8b3-483b-b75b-e8bc58516527
-- title:
--   Finite Format: format next eq
-- statement:
--   On a finite format, `Format.next b` is `b + 2^canonicalExp b` for `b ≥ 0`
--   (positive when there is no minimum quantum, where `next 0` is junk).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L255-L264
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L255-L264

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.format_next_eq (F : FiniteFormat) {b : _root_.Mpfx.Dyadic} (hb : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b = b + _root_.Mpfx.Dyadic.ofIntZpow 1 (F.canonicalExp ((b : _root_.Mpfx.Dyadic) : ℝ)) := by sorry
