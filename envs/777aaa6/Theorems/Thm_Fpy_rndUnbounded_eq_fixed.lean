-- Prove2me | Theorems.Thm_Fpy_rndUnbounded_eq_fixed
-- name    : Fpy.rndUnbounded_eq_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:34:01.729188+00:00
-- url     : https://prove2.me/theorems/77281206-7900-4e13-9201-55c4076e53b3
-- title:
--   Fpy: rnd Unbounded eq fixed
-- statement:
--   For `p ≠ 1`, rounding into `F` is rounding into a fixed-point format whose
--   quantum is `x`'s canonical exponent in `F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L83-L99
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Lower.lean#L83-L99

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.rndUnbounded_eq_fixed {F G : FiniteFormat} {rm : RoundingMode}
    (hp1 : F.p ≠ ((1 : ℕ) : Prec)) {x : ℝ} (hGp : G.p = ⊤)
    (hGe : G.exp = ((F.canonicalExp x : ℤ) : QExp)) (hF : ¬ F.IsUndefined rm)
    (hG : ¬ G.IsUndefined rm) : rndUnbounded G rm x hG = rndUnbounded F rm x hF := by sorry
