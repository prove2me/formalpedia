-- Prove2me | Theorems.Thm_Mpfx_floor_minimality
-- name    : Mpfx.floor_minimality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:59.37733+00:00
-- url     : https://prove2.me/theorems/29db58dc-c49d-4e4b-a9f4-d93ec3cc3b4f
-- title:
--   Mpfx: floor minimality
-- statement:
--   Generic floor-minimality: if `z ∈ F.unbounded` and `z ≤ x`, then `z` is
--   ≤ the floor-projection of `x` at the canonical exponent.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L21-L77
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L21-L77

import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_CanonicalExp
set_option autoImplicit true
open Mpfx

theorem Mpfx.floor_minimality (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hz_le_x : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) *
              (2 : ℝ) ^ (F.canonicalExp x) := by sorry
