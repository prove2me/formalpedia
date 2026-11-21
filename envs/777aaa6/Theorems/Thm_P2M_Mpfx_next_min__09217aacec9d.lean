-- Prove2me | Theorems.Thm_P2M_Mpfx_next_min__09217aacec9d
-- name    : P2M_Mpfx_next_min__09217aacec9d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:27.394573+00:00
-- url     : https://prove2.me/theorems/6bfa8f0f-325c-4dc7-a37f-2b9bda3e5752
-- title:
--   P2 M Mpfx next min  09217aacec9d: P2 M Mpfx next min  09217aacec9d
-- statement:
--   **Minimality of `next`**: for `b ≥ 0` in `F.unbounded`, any value of
--   `F.unbounded` strictly above `b` is at least `F.next b`. Without a minimum
--   quantum the base point must be positive, since `0` has no successor there.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L422-L458
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L422-L458

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_next_min__09217aacec9d {F : FiniteFormat} {b g : _root_.Mpfx.Dyadic}
    (hb_mem : b ∈ F.unbounded) (hg_mem : g ∈ F.unbounded)
    (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F.exp = ⊥ → 0 < ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hbg : ((b : _root_.Mpfx.Dyadic) : ℝ) < ((g : _root_.Mpfx.Dyadic) : ℝ)) :
    ((F.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ) ≤ ((g : _root_.Mpfx.Dyadic) : ℝ) := by sorry

alias «Mpfx».«next_min'» := P2M_Mpfx_next_min__09217aacec9d
