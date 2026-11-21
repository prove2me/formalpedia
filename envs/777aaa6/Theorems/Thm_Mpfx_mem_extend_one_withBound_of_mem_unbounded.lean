-- Prove2me | Theorems.Thm_Mpfx_mem_extend_one_withBound_of_mem_unbounded
-- name    : Mpfx.mem_extend_one_withBound_of_mem_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:45:04.402679+00:00
-- url     : https://prove2.me/theorems/bcbc66b0-4b58-415f-99d1-96b88a212fd2
-- title:
--   Mpfx: mem extend one with Bound of mem unbounded
-- statement:
--   Membership in `F₁.unbounded` plus the relaxed bound gives membership in the
--   paper containment format `(F₁.extend 1).withBound F₁.boundAfterNext`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L550-L555
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L550-L555

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem Mpfx.mem_extend_one_withBound_of_mem_unbounded {F₁ : FiniteFormat} {d : _root_.Mpfx.Dyadic}
    (hd : d ∈ F₁.unbounded)
    (hb : Format.boundOK F₁.toFormat.boundAfterNext d) :
    d ∈ ((F₁.extend 1).toFormat.withBound F₁.toFormat.boundAfterNext) := by sorry
