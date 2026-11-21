-- Prove2me | Theorems.Thm_Mpfx_withBound_subset_of_boundOK
-- name    : Mpfx.withBound_subset_of_boundOK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:03.733707+00:00
-- url     : https://prove2.me/theorems/444f7abd-313f-4f1f-87e2-d12e619950dc
-- title:
--   Mpfx: with Bound subset of bound OK
-- statement:
--   Bounding a format by a value that `B` admits keeps it within `B`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L129-L132
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L129-L132

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.withBound_subset_of_boundOK (F : Format) {B : Bound} {T : NonNegDyadic}
    (hT : Format.boundOK B T.val) : F.withBound (T : Bound) ⊆ F.withBound B := by sorry
