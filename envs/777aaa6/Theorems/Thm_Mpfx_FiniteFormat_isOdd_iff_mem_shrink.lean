-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_mem_shrink
-- name    : Mpfx.FiniteFormat.isOdd_iff_mem_shrink
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:52.329851+00:00
-- url     : https://prove2.me/theorems/a5f4186d-9586-4d77-ab6a-f2b018c5abc8
-- title:
--   Finite Format: is Odd iff mem shrink
-- statement:
--   **Odd values are the rest.** For `p ≠ 1`, `y` is odd exactly when it is a
--   value of `F` outside the shrink.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L218-L229
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L218-L229

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isOdd_iff_mem_shrink (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec))
    (y : Dyadic) :
    F.IsOdd y ↔ y ∈ F.unbounded ∧ y ∉ (F.shrink hp).unbounded := by sorry
