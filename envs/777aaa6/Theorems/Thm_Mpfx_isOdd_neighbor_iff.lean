-- Prove2me | Theorems.Thm_Mpfx_isOdd_neighbor_iff
-- name    : Mpfx.isOdd_neighbor_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:44:58.669748+00:00
-- url     : https://prove2.me/theorems/e1b6a583-a846-428d-b77f-28e7eb9ac4ba
-- title:
--   Mpfx: is Odd neighbor iff
-- statement:
--   For `p ≠ 1` and `x` off the canonical grid, a neighbour of `x` is odd
--   exactly when its significand is: it lies in the shrink exactly when its
--   significand is even.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L66-L88
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L66-L88

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
set_option autoImplicit true
open Mpfx

theorem Mpfx.isOdd_neighbor_iff {F : FiniteFormat} (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) :
    F.IsOdd (Dyadic.ofIntZpow m (F.canonicalExp x)) ↔ ¬ Even m := by sorry
