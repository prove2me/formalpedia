-- Prove2me | Theorems.Thm_Mpfx_Cex_exists_pred
-- name    : Mpfx.Cex.exists_pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:24.702089+00:00
-- url     : https://prove2.me/theorems/0345fb12-4774-4c21-8a4f-10d580915651
-- title:
--   Cex: exists pred
-- statement:
--   A positive value of `F` has an adjacent predecessor `u ≥ 0`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L111-L121
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L111-L121

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.exists_pred (F : FiniteFormat) {a : Dyadic} (ha : a ∈ F.unbounded)
    (ha_pos : (0 : ℝ) < a) : ∃ u : Dyadic, Adjacent F u a ∧ 0 ≤ (u : ℝ) := by sorry
