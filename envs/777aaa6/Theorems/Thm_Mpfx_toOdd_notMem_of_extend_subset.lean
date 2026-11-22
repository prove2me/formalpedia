-- Prove2me | Theorems.Thm_Mpfx_toOdd_notMem_of_extend_subset
-- name    : Mpfx.toOdd_notMem_of_extend_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:29.165452+00:00
-- url     : https://prove2.me/theorems/6e902870-286e-43f5-adf4-0ca78124e941
-- title:
--   Mpfx: to Odd not Mem of extend subset
-- statement:
--   **RTO-padding lemma, applied form.** From `F₁.extend 1 ⊆ F₂`, `2 ≤ F₂.p`, and
--   an RTO rounding `z` of `x` in `F₂` with `x ≠ z`, conclude `z ∉ F₁`. `F₁` is the shrink of
--   `F₁.extend 1`, so its values are even in `F₂`, while an inexact RTO result is
--   odd.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L147-L158
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Basic.lean#L147-L158

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_DoubleRounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.toOdd_notMem_of_extend_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.extend 1).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {x : ℝ} {z : Dyadic} (hz : RoundsFinite F₂ .toOdd x z)
    (hxne : x ≠ (z : ℝ)) :
    z ∉ F₁ := by sorry
