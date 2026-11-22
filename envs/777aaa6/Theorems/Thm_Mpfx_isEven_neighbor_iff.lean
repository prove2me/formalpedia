-- Prove2me | Theorems.Thm_Mpfx_isEven_neighbor_iff
-- name    : Mpfx.isEven_neighbor_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:50:59.317882+00:00
-- url     : https://prove2.me/theorems/04bd8be4-7c2b-4afe-90bc-00d0672cdc11
-- title:
--   Mpfx: is Even neighbor iff
-- statement:
--   For `p ≠ 1` and `x` off the canonical grid, a neighbour of `x` is even
--   exactly when its significand is.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L92-L101
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L92-L101

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
set_option autoImplicit true
open Mpfx

theorem Mpfx.isEven_neighbor_iff {F : FiniteFormat} (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ}
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x))
    {m : ℤ} (hm : m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ ∨
      m = ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) :
    F.IsEven (Dyadic.ofIntZpow m (F.canonicalExp x)) ↔ Even m := by sorry
