-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_nearest
-- name    : Mpfx.RoundsFinite.unique_nearest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:12.504033+00:00
-- url     : https://prove2.me/theorems/6cb465ee-6077-4c8b-8675-a3623e72c794
-- title:
--   Rounds Finite: unique nearest
-- statement:
--   Two nearest roundings are equidistant from `x`, so if they differ they sit
--   on opposite sides and the tie-break must separate them. It cannot: `.toEven`
--   would need both neighbours even, and `.awayZero` equal magnitudes across zero,
--   forcing `x = 0` where both roundings are `0`. Flocq `Rnd_NG_pt_unique`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L549-L623
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L549-L623

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_nearest {F : FiniteFormat} {tb : TieBreak} {x : ℝ}
    (h : ¬ F.IsUndefined (.nearest tb)) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded (.nearest tb) x y₁)
    (h₂ : RoundsFinite F.unbounded (.nearest tb) x y₂) :
    y₁ = y₂ := by sorry
