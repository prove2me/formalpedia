-- Prove2me | Theorems.Thm_P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc
-- name    : P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:32.01818+00:00
-- url     : https://prove2.me/theorems/5bfd0f43-9898-462f-b8a1-e2a10b094d32
-- title:
--   P2 M Mpfx next extend midpoint  cd09fcf4dbfc: P2 M Mpfx next extend midpoint  cd09fcf4dbfc
-- statement:
--   **`next` on `F₁.extend 1` is the midpoint**: extending by one bit halves the
--   step, so the finer successor lands halfway to the coarser one. Without a minimum
--   quantum the base point must be positive.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L481-L504
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Next.lean#L481-L504

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc {F₁ : FiniteFormat} {b : _root_.Mpfx.Dyadic}
    (hb_nn : 0 ≤ ((b : _root_.Mpfx.Dyadic) : ℝ))
    (hguard : F₁.exp = ⊥ → 0 < ((b : _root_.Mpfx.Dyadic) : ℝ)) :
    (((F₁.extend 1).toFormat.next b : _root_.Mpfx.Dyadic) : ℝ)
      = (((b : _root_.Mpfx.Dyadic) : ℝ) + ((F₁.toFormat.next b : _root_.Mpfx.Dyadic) : ℝ)) / 2 := by sorry

alias «Mpfx».«next_extend_midpoint'» := P2M_Mpfx_next_extend_midpoint__cd09fcf4dbfc
