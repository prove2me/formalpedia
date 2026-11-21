-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive
-- name    : Mpfx.RoundsFinite.unique_toPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:44:40.595914+00:00
-- url     : https://prove2.me/theorems/40a67a40-f0d9-4bdf-8051-693705fbc4bf
-- title:
--   Rounds Finite: unique to Positive
-- statement:
--   Flocq `Rnd_UP_pt_unique`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L231-L236
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L231-L236

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_toPositive {F : FiniteFormat} {x : ℝ} {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F .toPositive x y₁) (h₂ : RoundsFinite F .toPositive x y₂) :
    y₁ = y₂ := by sorry
