-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_cross
-- name    : Mpfx.IsFaithfulRound.cross
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:00.488247+00:00
-- url     : https://prove2.me/theorems/91f905da-f9ba-4718-8ada-4dbaee75d787
-- title:
--   Is Faithful Round: cross
-- statement:
--   Faithful roundings that cross put both inputs in one gap: `y'` rounds `x`
--   and `x'` down, `y` rounds both up, and `y' ≤ x ≤ x' < y`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L27-L42
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L27-L42

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.cross {F : FiniteFormat} {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x')
    (hy : IsFaithfulRound F x y) (hy' : IsFaithfulRound F x' y') (hlt : (y' : ℝ) < y) :
    RoundsFinite F .toPositive x y ∧ RoundsFinite F .toPositive x' y ∧
      RoundsFinite F .toNegative x y' ∧ RoundsFinite F .toNegative x' y' ∧
        x' < y ∧ (y' : ℝ) ≤ x := by sorry
