-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
-- name    : Mpfx.FiniteFormat.subset_unbounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:38:39.547176+00:00
-- url     : https://prove2.me/theorems/dc8685ad-0820-4a8f-82fe-78deff6739d3
-- title:
--   Finite Format: subset unbounded
-- statement:
--   Dropping the bound enlarges the format.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L492-L493
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L492-L493

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.subset_unbounded (F : FiniteFormat) : F.toFormat ⊆ F.unbounded.toFormat := by sorry
