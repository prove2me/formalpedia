-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_exp_eq_canonicalExp_of_p_one
-- name    : Mpfx.FiniteFormat.exp_eq_canonicalExp_of_p_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:43.451956+00:00
-- url     : https://prove2.me/theorems/c0f43112-a383-43a5-9df6-8c695034184c
-- title:
--   Finite Format: exp eq canonical Exp of p one
-- statement:
--   **Precision-`1` values odd in a wider format sit at the quantum.** If
--   `y ∈ F₁ ⊆ F₂` with `F₁.p = 1`, `F₂.p ≥ 2` and `y` odd in `F₂`, then `y`'s
--   exponent is `F₁.exp`: any higher power of two is even in `F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L338-L374
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L338-L374

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.exp_eq_canonicalExp_of_p_one {F₁ : FiniteFormat} {F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) (hp : ((2 : ℕ) : Prec) ≤ F₂.p)
    (hp₁ : F₁.p = ((1 : ℕ) : Prec)) {y : Dyadic} (hy : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.exp = ((F₁.canonicalExp y : ℤ) : QExp) := by sorry
