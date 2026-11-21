-- Prove2me | Theorems.Thm_Mpfx_Cex_Isolated_le_abs_sub
-- name    : Mpfx.Cex.Isolated.le_abs_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:47:16.878646+00:00
-- url     : https://prove2.me/theorems/3a88c98e-1bc1-4eda-a6c6-40fa88b8e156
-- title:
--   Isolated: le abs sub
-- statement:
--   Any other value of `F` is at least `2^K` from `m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L29-L31
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample/Basic.lean#L29-L31

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.Isolated.le_abs_sub {F : FiniteFormat} {m : Dyadic} {K : ℤ} (h : Isolated F m K)
    {v : Dyadic} (hv : v ∈ F.unbounded) (hne : v ≠ m) : (2 : ℝ) ^ K ≤ |(v : ℝ) - m| := by sorry
