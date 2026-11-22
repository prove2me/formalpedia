-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_unique_toOdd
-- name    : Mpfx.RoundsFinite.unique_toOdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:56:38.627087+00:00
-- url     : https://prove2.me/theorems/c00120ca-5a23-49e9-bad5-dc42ab28af51
-- title:
--   Rounds Finite: unique to Odd
-- statement:
--   Matching sides collapse by directed uniqueness; the mixed case would need
--   both neighbours odd, which `isOdd_alternate_of_bracketing` forbids.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L514-L541
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L514-L541

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.unique_toOdd {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded .toOdd x y₁)
    (h₂ : RoundsFinite F.unbounded .toOdd x y₂) :
    y₁ = y₂ := by sorry
