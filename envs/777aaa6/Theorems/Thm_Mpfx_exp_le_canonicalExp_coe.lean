-- Prove2me | Theorems.Thm_Mpfx_exp_le_canonicalExp_coe
-- name    : Mpfx.exp_le_canonicalExp_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:27:24.469223+00:00
-- url     : https://prove2.me/theorems/e9ff6505-d7c8-4e36-9f78-bfb394cf884f
-- title:
--   Mpfx: exp le canonical Exp coe
-- statement:
--   `F.exp ≤ (F.canonicalExp x : QExp)`, uniformly over `exp = ⊥`/finite.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L441-L445
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L441-L445

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.exp_le_canonicalExp_coe (F : FiniteFormat) (x : ℝ) :
    F.exp ≤ ((F.canonicalExp x : ℤ) : QExp) := by sorry
