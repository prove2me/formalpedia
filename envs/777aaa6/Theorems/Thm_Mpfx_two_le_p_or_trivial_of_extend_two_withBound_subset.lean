-- Prove2me | Theorems.Thm_Mpfx_two_le_p_or_trivial_of_extend_two_withBound_subset
-- name    : Mpfx.two_le_p_or_trivial_of_extend_two_withBound_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:54:52.089179+00:00
-- url     : https://prove2.me/theorems/434401fb-936c-4041-be7c-95345bc3fa1c
-- title:
--   Mpfx: two le p or trivial of extend two with Bound subset
-- statement:
--   The `k = 2` form of `two_le_p_or_trivial_of_extend_one_withBound_subset`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L669-L676
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L669-L676

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_le_p_or_trivial_of_extend_two_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    ((2 : ℕ) : Prec) ≤ F₂.p ∨ ∀ d : _root_.Mpfx.Dyadic, d ∈ F₁ → (d : ℝ) = 0 := by sorry
