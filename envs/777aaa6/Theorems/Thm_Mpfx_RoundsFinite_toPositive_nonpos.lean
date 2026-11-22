-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_toPositive_nonpos
-- name    : Mpfx.RoundsFinite.toPositive_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:25.095595+00:00
-- url     : https://prove2.me/theorems/2a1d170e-2485-41aa-8309-cbe5bcbb2fc7
-- title:
--   Rounds Finite: to Positive nonpos
-- statement:
--   Flocq `round_pred_le_0`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L648-L651
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L648-L651

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.toPositive_nonpos {F : FiniteFormat} {x : ℝ} (hx : x ≤ 0)
    {y : Dyadic} (h : RoundsFinite F .toPositive x y) : (y : ℝ) ≤ 0 := by sorry
