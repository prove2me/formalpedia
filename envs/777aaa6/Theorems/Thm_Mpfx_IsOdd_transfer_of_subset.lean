-- Prove2me | Theorems.Thm_Mpfx_IsOdd_transfer_of_subset
-- name    : Mpfx.IsOdd.transfer_of_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:55:47.081626+00:00
-- url     : https://prove2.me/theorems/ff851afe-f98e-49e1-8cf9-7eaf274e8e3d
-- title:
--   Is Odd: transfer of subset
-- statement:
--   **RTO-padding lemma.** If `F₁ ⊆ F₂`, `F₂.p ≥ 2`, and `y ∈ F₁` is odd in `F₂`,
--   then `y` is odd in `F₁`: were it even, it would be in `F₁`'s shrink, hence
--   even in `F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L382-L396
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L382-L396

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open FiniteFormat

theorem Mpfx.IsOdd.transfer_of_subset {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {y : Dyadic} (hyF₁ : y ∈ F₁) (hodd : F₂.IsOdd y) :
    F₁.IsOdd y := by sorry
