-- Prove2me | Theorems.Thm_Mpfx_neighbors_alternate
-- name    : Mpfx.neighbors_alternate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:22.237675+00:00
-- url     : https://prove2.me/theorems/36c23b26-67fc-46dc-ab47-004b5b455458
-- title:
--   Mpfx: neighbors alternate
-- statement:
--   **Adjacent values alternate in parity.** For `dlo = ⌊s⌋·2^e` and
--   `dhi = (⌊s⌋+1)·2^e` at the canonical exponent, `dhi` is odd exactly when `dlo`
--   is not. Flocq `DN_UP_parity_generic_pos`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L106-L169
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Parity.lean#L106-L169

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Parity
set_option autoImplicit true
open Mpfx

theorem Mpfx.neighbors_alternate {F : FiniteFormat} (x : ℝ)
    (h : ¬ F.IsUndefined .toOdd)
    (h_lo_ne_s :
      (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ : ℝ) ≠ x * (2 : ℝ) ^ (-F.canonicalExp x)) :
    F.IsOdd (Dyadic.ofIntZpow (⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ + 1) (F.canonicalExp x))
      ↔ ¬ F.IsOdd
        (Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-F.canonicalExp x)⌋ (F.canonicalExp x)) := by sorry
