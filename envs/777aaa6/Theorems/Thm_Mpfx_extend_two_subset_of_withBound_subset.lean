-- Prove2me | Theorems.Thm_Mpfx_extend_two_subset_of_withBound_subset
-- name    : Mpfx.extend_two_subset_of_withBound_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:40.918393+00:00
-- url     : https://prove2.me/theorems/ac459fad-7529-4dca-8d88-6c3011928ce7
-- title:
--   Mpfx: extend two subset of with Bound subset
-- statement:
--   The `k = 2` form of `extend_one_subset_of_withBound_subset`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L661-L666
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L661-L666

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.extend_two_subset_of_withBound_subset {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
              ⊆ F₂.toFormat) :
    (F₁.extend 2).toFormat ⊆ F₂.toFormat := by sorry
