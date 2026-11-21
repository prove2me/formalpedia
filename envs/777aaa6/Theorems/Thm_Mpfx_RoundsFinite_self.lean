-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_self
-- name    : Mpfx.RoundsFinite.self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:37.255476+00:00
-- url     : https://prove2.me/theorems/189fb20c-ea9b-4b51-940c-fe1523444bd8
-- title:
--   Rounds Finite: self
-- statement:
--   Every mode fixes a representable value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L367-L381
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L367-L381

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.self {F : FiniteFormat} (rm : RoundingMode) {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F rm (d : ℝ) d := by sorry
