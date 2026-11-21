-- Prove2me | Theorems.Thm_Mpfx_floor_mantissa_lt
-- name    : Mpfx.floor_mantissa_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:42:04.907654+00:00
-- url     : https://prove2.me/theorems/10ecb52e-2cad-42a5-8bdb-f8b81da5e31b
-- title:
--   Mpfx: floor mantissa lt
-- statement:
--   Canonical-mantissa bound: `|x · 2^(-canonicalExp x)| < 2^p` when `F.p`
--   is finite.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L103-L125
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/CanonicalExp.lean#L103-L125

import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_CanonicalExp
set_option autoImplicit true
open Mpfx

theorem Mpfx.floor_mantissa_lt {F : FiniteFormat} {x : ℝ}
    {p : ℕ} (hp : F.p = (p : Prec)) :
    |x * (2 : ℝ) ^ (-(F.canonicalExp x))| < (2 : ℝ) ^ p := by sorry
