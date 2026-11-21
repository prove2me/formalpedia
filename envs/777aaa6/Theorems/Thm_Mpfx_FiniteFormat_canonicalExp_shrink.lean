-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_shrink
-- name    : Mpfx.FiniteFormat.canonicalExp_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:40.426298+00:00
-- url     : https://prove2.me/theorems/67017888-c95b-43ab-aedf-83b116078537
-- title:
--   Finite Format: canonical Exp shrink
-- statement:
--   Shrinking raises the canonical exponent of every nonzero `x` by one.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L610-L633
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L610-L633

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.canonicalExp_shrink (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (hx : x ≠ 0) : (F.shrink h).canonicalExp x = F.canonicalExp x + 1 := by sorry
