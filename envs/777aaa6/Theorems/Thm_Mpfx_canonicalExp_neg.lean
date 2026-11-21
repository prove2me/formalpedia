-- Prove2me | Theorems.Thm_Mpfx_canonicalExp_neg
-- name    : Mpfx.canonicalExp_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:39.72471+00:00
-- url     : https://prove2.me/theorems/0cd68b05-3a75-4157-aba7-5c58d979f11f
-- title:
--   Mpfx: canonical Exp neg
-- statement:
--   `canonicalExp` depends only on `|·|`, hence is negation-invariant.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L468-L471
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L468-L471

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.canonicalExp_neg (F : FiniteFormat) (x : ℝ) :
    F.canonicalExp (-x) = F.canonicalExp x := by sorry
