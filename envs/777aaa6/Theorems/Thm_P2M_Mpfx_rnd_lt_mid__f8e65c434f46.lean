-- Prove2me | Theorems.Thm_P2M_Mpfx_rnd_lt_mid__f8e65c434f46
-- name    : P2M_Mpfx_rnd_lt_mid__f8e65c434f46
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:53:26.845647+00:00
-- url     : https://prove2.me/theorems/d33d0a66-d243-4d69-862b-9d0a33438ab2
-- title:
--   P2 M Mpfx rnd lt mid  f8e65c434f46: P2 M Mpfx rnd lt mid  f8e65c434f46
-- statement:
--   **Lemma 16 (Flocq `round_round_lt_mid_further_place`).** The hypothesis-free
--   form: binade consistency is derived from `hle` via `canonicalExp_eq_of_lt_mid`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L197-L207
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/NearestMidpoint.lean#L197-L207

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_rnd_lt_mid__f8e65c434f46 {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : _root_.Mpfx.Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by sorry

alias «Mpfx».«rnd_lt_mid'» := P2M_Mpfx_rnd_lt_mid__f8e65c434f46
