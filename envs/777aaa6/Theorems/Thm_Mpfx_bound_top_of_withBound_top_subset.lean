-- Prove2me | Theorems.Thm_Mpfx_bound_top_of_withBound_top_subset
-- name    : Mpfx.bound_top_of_withBound_top_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:44.171235+00:00
-- url     : https://prove2.me/theorems/b0d87a11-513c-4f4a-af40-9b3ef39b38c0
-- title:
--   Mpfx: bound top of with Bound top subset
-- statement:
--   If `F₁.withBound ⊤` is contained in `F₂`, then `F₂` has no finite bound:
--   `F₁.withBound ⊤` contains arbitrarily large powers of two.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L559-L561
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L559-L561

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.bound_top_of_withBound_top_subset {F₁ F₂ : FiniteFormat}
    (hsub : (F₁.toFormat.withBound ⊤) ⊆ F₂.toFormat) : F₂.b = ⊤ := by sorry
