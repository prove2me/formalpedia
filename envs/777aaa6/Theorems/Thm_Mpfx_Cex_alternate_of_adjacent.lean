-- Prove2me | Theorems.Thm_Mpfx_Cex_alternate_of_adjacent
-- name    : Mpfx.Cex.alternate_of_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:38.316606+00:00
-- url     : https://prove2.me/theorems/dfa541ea-4857-4bd4-bdd8-8b93096aa5db
-- title:
--   Cex: alternate of adjacent
-- statement:
--   Adjacent values alternate in parity: exactly one is odd, and one is even.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L124-L134
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L124-L134

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.alternate_of_adjacent (F : ParityFormat) {u u' : Dyadic}
    (h : Adjacent F.toFiniteFormat u u') :
    (F.IsOdd u' ↔ ¬ F.IsOdd u) ∧ (¬ F.IsEven u → F.IsEven u') := by sorry
