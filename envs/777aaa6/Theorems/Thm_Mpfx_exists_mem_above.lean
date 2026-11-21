-- Prove2me | Theorems.Thm_Mpfx_exists_mem_above
-- name    : Mpfx.exists_mem_above
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:57:38.47568+00:00
-- url     : https://prove2.me/theorems/1a497888-b0fa-43a1-9db0-eb4929037112
-- title:
--   Mpfx: exists mem above
-- statement:
--   A value of `F` above `b ≥ 0` and at most `next b`: the successor of `b`'s
--   floor at its canonical step.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L136-L171
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Total.lean#L136-L171

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
set_option autoImplicit true
open Mpfx

theorem Mpfx.exists_mem_above {F : FiniteFormat} {b : Dyadic} (hb : 0 ≤ (b : ℝ)) :
    ∃ N : Dyadic, N ∈ F.unbounded ∧ (b : ℝ) < N ∧ (N : ℝ) ≤ F.toFormat.next b := by sorry
