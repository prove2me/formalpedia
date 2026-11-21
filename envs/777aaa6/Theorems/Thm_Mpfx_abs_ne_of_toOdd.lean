-- Prove2me | Theorems.Thm_Mpfx_abs_ne_of_toOdd
-- name    : Mpfx.abs_ne_of_toOdd
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:54:08.942869+00:00
-- url     : https://prove2.me/theorems/86ee117b-26b0-4b1c-a7d0-eef903e32830
-- title:
--   Mpfx: abs ne of to Odd
-- statement:
--   **RTO padding at a value of `F₁.extend 1`.** Under the RN containment, an
--   inexact RTO rounding into `F₂` never has the magnitude of a value `v` of
--   `F₁.extend 1` within `next(b₁)`: `F₁.extend 1` there is the shrink of a subformat
--   of `F₂`, so `±v` is even in `F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L295-L315
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L295-L315

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_ne_of_toOdd {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p) {x : ℝ} {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded .toOdd x z) (hxz : x ≠ (z : ℝ)) {v : Dyadic}
    (hv : v ∈ (F₁.extend 1).unbounded)
    (hvB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext v) :
    |(z : ℝ)| ≠ |(v : ℝ)| := by sorry
