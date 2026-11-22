-- Prove2me | Theorems.Thm_Mpfx_Cex_exists_isolated_le
-- name    : Mpfx.Cex.exists_isolated_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:22.223011+00:00
-- url     : https://prove2.me/theorems/890264f7-c876-4365-a720-6c41ec3b137b
-- title:
--   Cex: exists isolated le
-- statement:
--   A format is isolated at a positive dyadic `m` with `K` small enough that
--   `2^K ≤ m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L87-L92
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L87-L92

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.exists_isolated_le (F : FiniteFormat) {m : Dyadic} (hm : (0 : ℝ) < m) :
    ∃ K : ℤ, Isolated F m K ∧ (2 : ℝ) ^ K ≤ m := by sorry
