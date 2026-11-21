-- Prove2me | Theorems.Thm_Mpfx_boundOK_boundAfterNext_next
-- name    : Mpfx.boundOK_boundAfterNext_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:01.201661+00:00
-- url     : https://prove2.me/theorems/8e0f7386-bbd7-4e46-95c3-a28b2055b220
-- title:
--   Mpfx: bound OK bound After Next next
-- statement:
--   `next(b₁)` satisfies the relaxed bound `boundAfterNext`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L512-L522
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L512-L522

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.boundOK_boundAfterNext_next {F₁ : FiniteFormat} {b₁ : NonNegDyadic}
    (hF₁b : F₁.b = (b₁ : Bound))
    (hN_nn : 0 ≤ ((F₁.toFormat.next b₁.val : _root_.Mpfx.Dyadic) : ℝ)) :
    Format.boundOK F₁.toFormat.boundAfterNext (F₁.toFormat.next b₁.val) := by sorry
