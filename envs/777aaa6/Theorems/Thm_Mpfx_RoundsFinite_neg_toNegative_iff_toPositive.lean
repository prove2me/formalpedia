-- Prove2me | Theorems.Thm_Mpfx_RoundsFinite_neg_toNegative_iff_toPositive
-- name    : Mpfx.RoundsFinite.neg_toNegative_iff_toPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:48:24.060183+00:00
-- url     : https://prove2.me/theorems/802bdcd9-c44c-4edc-ba8d-b27ab87cc2e8
-- title:
--   Rounds Finite: neg to Negative iff to Positive
-- statement:
--   Sign-symmetry: `.toNegative` ↔ `.toPositive` swaps under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L72-L78
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L72-L78

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.RoundsFinite.neg_toNegative_iff_toPositive (F : FiniteFormat) (x : ℝ)
    (y : Dyadic) :
    RoundsFinite F .toNegative x y ↔ RoundsFinite F .toPositive (-x) (-y) := by sorry
