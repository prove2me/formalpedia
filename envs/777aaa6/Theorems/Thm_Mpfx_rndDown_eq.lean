-- Prove2me | Theorems.Thm_Mpfx_rndDown_eq
-- name    : Mpfx.rndDown_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:45:36.375324+00:00
-- url     : https://prove2.me/theorems/105794fa-c2d6-4201-8bec-dc52f043a40e
-- title:
--   Mpfx: rnd Down eq
-- statement:
--   `⌊x·2^(−e)⌋·2^e` at `e = canonicalExp x`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L47-L49
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L47-L49

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_eq (F : FiniteFormat) (x : ℝ) :
    rndDown F x =
      Dyadic.ofIntZpow ⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ (F.canonicalExp x) := by sorry
