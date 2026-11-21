-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
-- name    : Mpfx.RoundsFinite.unique_toNegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:00.760178+00:00
-- url     : https://prove2.me/theorems/d086ce9d-e5a1-464a-8e27-ab2b1cd8f280
-- title:
--   Rounds Finite: unique to Negative
-- statement:
--   Two largest `F`-elements `≤ x` coincide (Flocq `Rnd_DN_pt_unique`).
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L223-L228
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L223-L228

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_toNegative {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toNegative x y₁) (h₂ : RoundsFinite F .toNegative x y₂) :
    y₁ = y₂ := by sorry
