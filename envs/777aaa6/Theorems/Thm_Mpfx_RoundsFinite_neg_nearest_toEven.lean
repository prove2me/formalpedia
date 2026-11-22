-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_nearest_toEven
-- name    : Mpfx.RoundsFinite.neg_nearest_toEven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:53.174777+00:00
-- url     : https://prove2.me/theorems/2947082f-9307-4b95-a549-ded8f59062d1
-- title:
--   Rounds Finite: neg nearest to Even
-- statement:
--   Sign-symmetry of `RoundsFinite` at mode `.nearest .toEven`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L100-L109
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L100-L109

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_nearest_toEven (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .toEven) x y ↔
      RoundsFinite F (.nearest .toEven) (-x) (-y) := by sorry
