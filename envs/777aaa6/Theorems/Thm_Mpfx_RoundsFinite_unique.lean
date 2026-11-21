-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique
-- name    : Mpfx.RoundsFinite.unique
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:43:33.209425+00:00
-- url     : https://prove2.me/theorems/839baab4-2c9a-49c2-a81c-55dcd189a0cc
-- title:
--   Rounds Finite: unique
-- statement:
--   The spec pins its value, for every mode (Flocq `round_unique`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L626-L637
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L626-L637

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded rm x y₁)
    (h₂ : RoundsFinite F.unbounded rm x y₂) :
    y₁ = y₂ := by sorry
