-- Prove2me | Theorems.Thm_Mpfx_extend_one_subset_of_withBound_subset
-- name    : Mpfx.extend_one_subset_of_withBound_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:19.450326+00:00
-- url     : https://prove2.me/theorems/5408e4d7-236a-429a-886e-6790654dbaab
-- title:
--   Mpfx: extend one subset of with Bound subset
-- statement:
--   `(F₁.extend 1).withBound F₁.boundAfterNext ⊆ F₂` implies
--   `F₁.extend 1 ⊆ F₂`, since `next(b₁) ≥ b₁`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L577-L580
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L577-L580

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.extend_one_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) ⊆ F₂.toFormat) :
    (F₁.extend 1).toFormat ⊆ F₂.toFormat := by sorry
