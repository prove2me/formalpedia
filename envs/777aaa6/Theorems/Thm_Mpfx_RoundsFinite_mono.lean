-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_mono
-- name    : Mpfx.RoundsFinite.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:58:56.570687+00:00
-- url     : https://prove2.me/theorems/a247fd9a-4234-4b42-a1fc-4cc1f6aa96fb
-- title:
--   Rounds Finite: mono
-- statement:
--   **Rounding is monotone**, in every mode.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L45-L87
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Monotone.lean#L45-L87

import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Monotone
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.mono {F : FiniteFormat} {rm : RoundingMode} (h : ¬ F.IsUndefined rm)
    {x x' : ℝ} {y y' : Dyadic} (hx : x ≤ x') (hy : RoundsFinite F.unbounded rm x y)
    (hy' : RoundsFinite F.unbounded rm x' y') : (y : ℝ) ≤ y' := by sorry
