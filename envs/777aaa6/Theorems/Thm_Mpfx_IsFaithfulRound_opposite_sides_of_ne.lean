-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_opposite_sides_of_ne
-- name    : Mpfx.IsFaithfulRound.opposite_sides_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:25.803173+00:00
-- url     : https://prove2.me/theorems/940f2977-f996-4668-964d-e0dce13ec4f8
-- title:
--   Is Faithful Round: opposite sides of ne
-- statement:
--   Two *distinct* faithful roundings sit on opposite sides of `x`; same-side
--   pairs collapse by uniqueness. The case split behind `unique_nearest`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L305-L315
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L305-L315

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.opposite_sides_of_ne {F : FiniteFormat} {x : ℝ}
    {a b : Dyadic} (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b)
    (hab : a ≠ b) :
    (RoundsFinite F .toNegative x a ∧ RoundsFinite F .toPositive x b) ∨
    (RoundsFinite F .toNegative x b ∧ RoundsFinite F .toPositive x a) := by sorry
