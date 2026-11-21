-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
-- name    : Mpfx.FiniteFormat.unbounded_isUndefined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:35.940566+00:00
-- url     : https://prove2.me/theorems/102d3000-9af4-4ebe-a236-d568902f3098
-- title:
--   Finite Format: unbounded is Undefined
-- statement:
--   `IsUndefined` depends only on `(F.p, F.exp)`, both preserved by
--   `F.unbounded`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L67-L69
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L67-L69

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.FiniteFormat.unbounded_isUndefined (F : FiniteFormat)
    (rm : RoundingMode) :
    F.unbounded.IsUndefined rm = F.IsUndefined rm := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_isUndefined
