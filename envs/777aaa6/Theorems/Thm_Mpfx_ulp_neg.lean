-- Prove2me | Theorems.Thm_Mpfx_ulp_neg
-- name    : Mpfx.ulp_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:55.98439+00:00
-- url     : https://prove2.me/theorems/c2c5244c-a12e-419a-9746-6c5bda8aca00
-- title:
--   Mpfx: ulp neg
-- statement:
--   The Mpfx construction uses the ulp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L38-L39
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L38-L39

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.ulp_neg (F : FiniteFormat) (x : ℝ) : ulp F (-x) = ulp F x := by sorry
