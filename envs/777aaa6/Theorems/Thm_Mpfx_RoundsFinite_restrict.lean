-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_restrict
-- name    : Mpfx.RoundsFinite.restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:57:45.502073+00:00
-- url     : https://prove2.me/theorems/5af2f9a6-2ad9-4488-8e88-eb0c56ea2155
-- title:
--   Rounds Finite: restrict
-- statement:
--   **Restrict**: an in-bound unbounded rounding is also the bounded rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Restrict.lean#L224-L233
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Restrict.lean#L224-L233

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Restrict
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.restrict {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    {y : Dyadic} (h : RoundsFinite F.unbounded rm x y)
    (hb : Format.boundOK F.b y) : RoundsFinite F rm x y := by sorry
