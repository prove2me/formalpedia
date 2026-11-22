-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_ofIntZpow_of_p_one
-- name    : Mpfx.FiniteFormat.canonicalExp_ofIntZpow_of_p_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:17.371877+00:00
-- url     : https://prove2.me/theorems/7a9263cf-41ad-4314-b902-3fa6af09c5f6
-- title:
--   Finite Format: canonical Exp of Int Zpow of p one
-- statement:
--   At precision `1`, `±2^j` above the quantum is its own canonical step.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L279-L286
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L279-L286

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.canonicalExp_ofIntZpow_of_p_one {F : FiniteFormat} (hp : F.p = ((1 : ℕ) : Prec))
    {e₀ : ℤ} (he : F.exp = (e₀ : QExp)) {k j : ℤ} (hk : |k| = 1) (hj : e₀ ≤ j) :
    F.canonicalExp (Dyadic.ofIntZpow k j) = j := by sorry
