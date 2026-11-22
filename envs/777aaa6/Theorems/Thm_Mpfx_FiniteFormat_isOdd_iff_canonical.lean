-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isOdd_iff_canonical
-- name    : Mpfx.FiniteFormat.isOdd_iff_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:16.489514+00:00
-- url     : https://prove2.me/theorems/25b19726-4242-40a0-a2cc-ce37b6f9624f
-- title:
--   Finite Format: is Odd iff canonical
-- statement:
--   `IsOdd` at the canonical exponent: `y ≠ 0` is `c · 2^cexp y` with `c` odd,
--   or, at precision `1`, its exponent has odd index above `exp`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L159-L168
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L159-L168

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isOdd_iff_canonical (F : FiniteFormat) (y : Dyadic) :
    F.IsOdd y ↔ (y : ℝ) ≠ 0 ∧ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧
      if F.p = ((1 : ℕ) : Prec) then
        Odd (F.canonicalExp y - WithBot.unbotD 0 F.exp + 1) else Odd c := by sorry
