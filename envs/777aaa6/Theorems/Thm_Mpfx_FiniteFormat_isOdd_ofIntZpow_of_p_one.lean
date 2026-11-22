-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isOdd_ofIntZpow_of_p_one
-- name    : Mpfx.FiniteFormat.isOdd_ofIntZpow_of_p_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:55:22.924113+00:00
-- url     : https://prove2.me/theorems/1affb0c5-5135-4397-996e-465ad394fa70
-- title:
--   Finite Format: is Odd of Int Zpow of p one
-- statement:
--   At precision `1`, `±2^j` is odd when `j` has even index above `exp`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L290-L298
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L290-L298

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isOdd_ofIntZpow_of_p_one (F : FiniteFormat) (hp : F.p = ((1 : ℕ) : Prec))
    {e₀ : ℤ} (he : F.exp = (e₀ : QExp)) {k j : ℤ} (hk : |k| = 1) (hj : e₀ ≤ j) :
    F.IsOdd (Dyadic.ofIntZpow k j) ↔ Even (j - e₀) := by sorry
