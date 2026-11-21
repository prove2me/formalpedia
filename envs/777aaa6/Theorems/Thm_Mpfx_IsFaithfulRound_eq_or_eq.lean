-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_eq_or_eq
-- name    : Mpfx.IsFaithfulRound.eq_or_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:45:17.972696+00:00
-- url     : https://prove2.me/theorems/9f6b109f-55c3-47e9-8ffb-b7d080a1424c
-- title:
--   Is Faithful Round: eq or eq
-- statement:
--   A faithful rounding is the round-down or the round-up.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L318-L321
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L318-L321

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.eq_or_eq {F : FiniteFormat} {x : ℝ} {d u y : Dyadic}
    (hd : RoundsFinite F .toNegative x d) (hu : RoundsFinite F .toPositive x u)
    (h : IsFaithfulRound F x y) : y = d ∨ y = u := by sorry
