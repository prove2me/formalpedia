-- Prove2me | Theorems.Thm_P2M_Mpfx_Cex_exists_isolated__0de9343c9367
-- name    : P2M_Mpfx_Cex_exists_isolated__0de9343c9367
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:23.183177+00:00
-- url     : https://prove2.me/theorems/f13e704a-ab1d-4360-948c-7e8f006722b3
-- title:
--   P2 M Mpfx Cex exists isolated  0de9343c9367: P2 M Mpfx Cex exists isolated  0de9343c9367
-- statement:
--   Two formats are isolated at a positive dyadic `m` with a common `K`, small
--   enough that `2^K ≤ m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L96-L101
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L96-L101

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem P2M_Mpfx_Cex_exists_isolated__0de9343c9367 (F G : FiniteFormat) {m : _root_.Mpfx.Dyadic} (hm : (0 : ℝ) < m) :
    ∃ K : ℤ, Isolated F m K ∧ Isolated G m K ∧ (2 : ℝ) ^ K ≤ m := by sorry

alias «Mpfx».«Cex».«exists_isolated₂» := P2M_Mpfx_Cex_exists_isolated__0de9343c9367
