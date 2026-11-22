-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isEven_iff_mem_shrink
-- name    : Mpfx.FiniteFormat.isEven_iff_mem_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:21.701541+00:00
-- url     : https://prove2.me/theorems/50db8d71-adaa-49fc-ba30-d18a98619da2
-- title:
--   Finite Format: is Even iff mem shrink
-- statement:
--   **Even values are the shrink.** For `p ≠ 1`, `y` is even exactly when it
--   is a value of `𝒜(p − 1, exp + 1)`: an even significand at `cexp y` is a
--   significand at `cexp y + 1`, the shrink's canonical exponent.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L198-L214
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L198-L214

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isEven_iff_mem_shrink (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec))
    (y : Dyadic) : F.IsEven y ↔ y ∈ (F.shrink hp).unbounded := by sorry
