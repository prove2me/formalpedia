-- Prove2me | Theorems.Thm_Mpfx_abs_faithful_le_of_le
-- name    : Mpfx.abs_faithful_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:43:54.306302+00:00
-- url     : https://prove2.me/theorems/ffddcb1a-02a5-409c-a6c1-303fa859ac04
-- title:
--   Mpfx: abs faithful le of le
-- statement:
--   A faithful rounding of `x` lies in `[-N, N]` once `|x| ≤ N ∈ F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L689-L708
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L689-L708

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.abs_faithful_le_of_le {F : FiniteFormat} {x : ℝ} {z N : Dyadic}
    (hN_mem : N ∈ F) (hxN : |x| ≤ (N : ℝ))
    (hfaithful : IsFaithfulRound F x z) :
    |(z : ℝ)| ≤ (N : ℝ) := by sorry
