-- Prove2me | Theorems.Thm_Mpfx_Cex_exists_isolated
-- name    : Mpfx.Cex.exists_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:53.414701+00:00
-- url     : https://prove2.me/theorems/52909b20-3c94-4f54-b3fd-5e6d8144d3e4
-- title:
--   Cex: exists isolated
-- statement:
--   **Discreteness away from zero.** Every format is isolated at every nonzero
--   dyadic `m`: its values of magnitude at least `|m|/2` are multiples of the step
--   there (`exists_mul_zpow_canonicalExp`, `canonicalExp_mono`), and so is `m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L44-L83
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L44-L83

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.exists_isolated (F : FiniteFormat) {m : Dyadic} (hm : (m : ℝ) ≠ 0) :
    ∃ K : ℤ, Isolated F m K := by sorry
