-- Prove2me | Theorems.Thm_Mpfx_rndUp_eq
-- name    : Mpfx.rndUp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:39.496874+00:00
-- url     : https://prove2.me/theorems/dbeba7dd-36ce-4197-9b91-953aae153561
-- title:
--   Mpfx: rnd Up eq
-- statement:
--   `⌈x·2^(−e)⌉·2^e`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L272-L274
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L272-L274

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndUp_eq (F : FiniteFormat) (x : ℝ) :
    rndUp F x =
      Dyadic.ofIntZpow ⌈x * (2 : ℝ) ^ (-(F.canonicalExp x))⌉ (F.canonicalExp x) := by sorry
