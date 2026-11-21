-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
-- name    : Mpfx.FiniteFormat.canonicalExp_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:26:40.803703+00:00
-- url     : https://prove2.me/theorems/c1aae44a-f923-4c02-9b1b-dbeaa150e329
-- title:
--   Finite Format: canonical Exp mono
-- statement:
--   `canonicalExp` is monotone in magnitude.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L377-L385
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L377-L385

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.canonicalExp_mono (F : FiniteFormat) {y z : ℝ} (hy : y ≠ 0)
    (hyz : |y| ≤ |z|) : F.canonicalExp y ≤ F.canonicalExp z := by sorry
