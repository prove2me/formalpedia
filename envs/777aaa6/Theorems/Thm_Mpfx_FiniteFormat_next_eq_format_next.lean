-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_next_eq_format_next
-- name    : Mpfx.FiniteFormat.next_eq_format_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:36.220187+00:00
-- url     : https://prove2.me/theorems/4ebcd49a-407c-4f16-b31c-50564d02108a
-- title:
--   Finite Format: next eq format next
-- statement:
--   On positive arguments the two successors agree: `Format.next`'s step
--   exponent `max exp (⌊log₂ b⌋ − p + 1)` *is* `canonicalExp b`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L234-L251
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L234-L251

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.next_eq_format_next (F : FiniteFormat) {b : _root_.Mpfx.Dyadic}
    (hb : 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) : F.toFormat.next b = F.next b := by sorry
