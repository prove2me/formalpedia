-- Prove2me | Theorems.Thm_Mpfx_two_le_p_of_nontrivial_extend_two
-- name    : Mpfx.two_le_p_of_nontrivial_extend_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:48:04.874036+00:00
-- url     : https://prove2.me/theorems/14f72287-53d2-4050-a6d7-2be7b80f1ff4
-- title:
--   Mpfx: two le p of nontrivial extend two
-- statement:
--   RN variant of `two_le_p_of_nontrivial`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L679-L685
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L679-L685

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.two_le_p_of_nontrivial_extend_two {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) : ((2 : ℕ) : Prec) ≤ F₂.p := by sorry
