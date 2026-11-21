-- Prove2me | Theorems.Thm_Mpfx_Format_two_le_p_of_precision_two_witness
-- name    : Mpfx.Format.two_le_p_of_precision_two_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:43.680121+00:00
-- url     : https://prove2.me/theorems/e4289704-1a30-4d72-9ee7-bf935765fe75
-- title:
--   Format: two le p of precision two witness
-- statement:
--   A `Dyadic` not representable in 1 bit cannot live in a format with
--   `F.p ≤ 1`, so a precision-2 witness in `F` forces `F.p ≥ 2`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L472-L485
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L472-L485

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.Format

theorem Mpfx.Format.two_le_p_of_precision_two_witness {F : Format} {v : Dyadic}
    (hvF : v ∈ F) (hv_not_p1 : ¬ Dyadic.precisionAtMost ((1 : ℕ) : Prec) v) :
    ((2 : ℕ) : Prec) ≤ F.p := by sorry
