-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_nearest_awayZero
-- name    : Mpfx.RoundsFinite.neg_nearest_awayZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:47.719151+00:00
-- url     : https://prove2.me/theorems/08d526ba-0e6b-4090-9ea7-89d34e3b7f7a
-- title:
--   Rounds Finite: neg nearest away Zero
-- statement:
--   Sign-symmetry of `RoundsFinite` at mode `.nearest .awayZero`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L89-L97
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L89-L97

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_nearest_awayZero (F : FiniteFormat) (x : ℝ) (y : Dyadic) :
    RoundsFinite F (.nearest .awayZero) x y ↔
      RoundsFinite F (.nearest .awayZero) (-x) (-y) := by sorry
