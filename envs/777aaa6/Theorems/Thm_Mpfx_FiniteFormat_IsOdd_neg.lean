-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg
-- name    : Mpfx.FiniteFormat.IsOdd.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:16.550982+00:00
-- url     : https://prove2.me/theorems/e69e7cd3-591b-45bb-ac1c-bc678083cea1
-- title:
--   Is Odd: neg
-- statement:
--   `IsOdd` is invariant under negation.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L52-L65
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Parity.lean#L52-L65

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.IsOdd.neg {F : FiniteFormat} {y : Dyadic} (h : IsOdd F y) :
    IsOdd F (-y) := by sorry
