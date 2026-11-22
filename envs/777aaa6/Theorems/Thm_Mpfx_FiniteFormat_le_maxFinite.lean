-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_le_maxFinite
-- name    : Mpfx.FiniteFormat.le_maxFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:29:18.012099+00:00
-- url     : https://prove2.me/theorems/f6636594-e51a-47ec-852b-9bcdb1433ab2
-- title:
--   Finite Format: le max Finite
-- statement:
--   Every value of a bounded `F` is at most `maxFinite`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L38-L44
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Special.lean#L38-L44

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.le_maxFinite (F : FiniteFormat) (hb : F.b ≠ ⊤) {v : Dyadic} (hv : v ∈ F) :
    (v : ℝ) ≤ (F.maxFinite hb : ℝ) := by sorry
