-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
-- name    : Mpfx.RoundsFinite.eq_zero_of_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:54.419268+00:00
-- url     : https://prove2.me/theorems/80742541-95ea-4217-951f-ff289482ccbf
-- title:
--   Rounds Finite: eq zero of zero
-- statement:
--   Every mode sends `0` to `0` (Flocq `round_0`),
--   since `0` lies in every format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L299-L301
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L299-L301

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.eq_zero_of_zero {F : FiniteFormat} {rm : RoundingMode}
    {y : Dyadic} (h : RoundsFinite F rm 0 y) : y = 0 := by sorry
