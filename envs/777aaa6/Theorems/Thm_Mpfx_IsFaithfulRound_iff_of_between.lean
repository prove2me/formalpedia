-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_iff_of_between
-- name    : Mpfx.IsFaithfulRound.iff_of_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:14.17021+00:00
-- url     : https://prove2.me/theorems/9e000802-9b3f-4097-94ae-251bfae29be3
-- title:
--   Is Faithful Round: iff of between
-- statement:
--   **Shared neighbours.** If `z` is a faithful rounding of `x` in `F₂ ⊇ F₁` and
--   not a value of `F₁`, then `x` and `z` have the same faithful roundings in `F₁`:
--   no value of `F₁` separates them.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L404-L425
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L404-L425

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.iff_of_between {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {z : Dyadic}
    (hz : IsFaithfulRound F₂ x z) (hz₁ : z ∉ F₁) (c : Dyadic) :
    IsFaithfulRound F₁ x c ↔ IsFaithfulRound F₁ z c := by sorry
