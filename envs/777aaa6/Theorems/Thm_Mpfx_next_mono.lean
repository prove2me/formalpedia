-- Prove2me | Theorems.Thm_Mpfx_next_mono
-- name    : Mpfx.next_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:56.052392+00:00
-- url     : https://prove2.me/theorems/8a7b08a9-c46e-46e5-b090-e691094a57c8
-- title:
--   Mpfx: next mono
-- statement:
--   `next` is monotone on `[0, ∞)` (for `exp = ⊥` the smaller point must be
--   positive, since `next` is junk at `0` there): the step `2^canonicalExp` grows
--   with the base.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L463-L476
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L463-L476

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.next_mono {F : FiniteFormat} {d b : _root_.Mpfx.Dyadic} (hd : 0 ≤ ((d : _root_.Mpfx.Dyadic) : ℝ))
    (hdb : ((d : _root_.Mpfx.Dyadic) : ℝ) ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((d : _root_.Mpfx.Dyadic) : ℝ)) :
    ((F.toFormat.next d : _root_.Mpfx.Dyadic) : ℝ) ≤ ((F.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ) := by sorry
