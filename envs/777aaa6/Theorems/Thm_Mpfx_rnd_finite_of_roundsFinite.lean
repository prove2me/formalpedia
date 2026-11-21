-- Prove2me | Theorems.Thm_Mpfx_rnd_finite_of_roundsFinite
-- name    : Mpfx.rnd_finite_of_roundsFinite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:15.442189+00:00
-- url     : https://prove2.me/theorems/f7f34505-60ea-454a-8b3e-8c661e2efe39
-- title:
--   Mpfx: rnd finite of rounds Finite
-- statement:
--   `rnd` on a real, read off any witness of the unbounded rounding.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L93-L100
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Op.lean#L93-L100

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable

theorem Mpfx.rnd_finite_of_roundsFinite {F : FiniteFormat} {S : SpecialMap F.toFormat}
    {O : OverflowMap F.toFormat} {rm : RoundingMode} {x : ℝ} {y : Dyadic}
    (h : ¬ F.IsUndefined rm) (hy : RoundsFinite F.unbounded rm x y) :
    rnd F S O rm (.finite x) =
      if Format.boundOK F.b y then .value (.finite y)
      else .value (O.map (decide ((y : ℚ) < 0))) := by sorry
