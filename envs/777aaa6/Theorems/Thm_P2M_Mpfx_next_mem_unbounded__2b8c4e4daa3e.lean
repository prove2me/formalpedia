-- Prove2me | Theorems.Thm_P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
-- name    : P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:44.681854+00:00
-- url     : https://prove2.me/theorems/743af24d-f7d1-4f15-ac8c-23571c36f620
-- title:
--   P2 M Mpfx next mem unbounded  2b8c4e4daa3e: P2 M Mpfx next mem unbounded  2b8c4e4daa3e
-- statement:
--   **Closure of `next`**: if `b ≥ 0` is in `F.unbounded`, so is `F.next b`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L368-L417
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L368-L417

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e {F : FiniteFormat} {b : _root_.Mpfx.Dyadic}
    (hb_mem : b ∈ F.unbounded) (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    F.toFormat.next b ∈ F.unbounded := by sorry

alias «Mpfx».«next_mem_unbounded'» := P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
