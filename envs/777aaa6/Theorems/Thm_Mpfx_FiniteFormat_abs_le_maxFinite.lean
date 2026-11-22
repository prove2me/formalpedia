-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_abs_le_maxFinite
-- name    : Mpfx.FiniteFormat.abs_le_maxFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:29:32.220939+00:00
-- url     : https://prove2.me/theorems/3243a945-2d62-4899-adde-a6f9376a2d6e
-- title:
--   Finite Format: abs le max Finite
-- statement:
--   Every value of a bounded `F` is at most `maxFinite` in magnitude.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L47-L52
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L47-L52

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.abs_le_maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    |(v : ℝ)| ≤ (F.maxFinite hb : ℝ) := by sorry
