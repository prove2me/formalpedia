-- Prove2me | Theorems.Thm_Mpfx_IsFaithfulRound_of_subset
-- name    : Mpfx.IsFaithfulRound.of_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:30.188298+00:00
-- url     : https://prove2.me/theorems/a5935f2e-8240-4fd5-ab1c-0f8de36d8c1d
-- title:
--   Is Faithful Round: of subset
-- statement:
--   A faithful rounding that lies in a smaller format is faithful there: the
--   smaller format has fewer candidates.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L385-L388
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L385-L388

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.IsFaithfulRound.of_subset {F₁ F₂ : FiniteFormat} (hsub : F₁.toFormat ⊆ F₂.toFormat)
    {x : ℝ} {y : Dyadic} (h : IsFaithfulRound F₂ x y) (hy : y ∈ F₁) : IsFaithfulRound F₁ x y := by sorry
