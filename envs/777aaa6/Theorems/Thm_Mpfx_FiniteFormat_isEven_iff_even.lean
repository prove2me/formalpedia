-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_isEven_iff_even
-- name    : Mpfx.FiniteFormat.isEven_iff_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:50:51.280189+00:00
-- url     : https://prove2.me/theorems/ebf4a8aa-92a0-491a-8397-bf094239e04b
-- title:
--   Finite Format: is Even iff even
-- statement:
--   For `p ≠ 1`, `y` is even iff its significand at the canonical exponent is.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L180-L191
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L180-L191

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.isEven_iff_even (F : FiniteFormat) (hp : F.p ≠ ((1 : ℕ) : Prec)) (y : Dyadic) :
    F.IsEven y ↔ ∃ c : ℤ, (y : ℝ) = c * 2 ^ F.canonicalExp y ∧ Even c := by sorry
