-- Prove2me | Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
-- name    : Mpfx.isFaithfulRound_iff_directed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:39.791552+00:00
-- url     : https://prove2.me/theorems/7a7455b0-1c91-4b0b-9a5d-515c6254351c
-- title:
--   Mpfx: is Faithful Round iff directed
-- statement:
--   `IsFaithfulRound` is exactly "round-down or round-up", phrased via the
--   directed `RoundsFinite` specs (by definition). This lets the round-to-nearest machinery work
--   with `RoundsFinite .toNegative/.toPositive` while the `.nearest` spec hands
--   out an `IsFaithfulRound`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L45-L48
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L45-L48

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.isFaithfulRound_iff_directed {F : FiniteFormat} {x : ℝ} {y : Dyadic} :
    IsFaithfulRound F x y ↔
      RoundsFinite F .toNegative x y ∨ RoundsFinite F .toPositive x y := by sorry
