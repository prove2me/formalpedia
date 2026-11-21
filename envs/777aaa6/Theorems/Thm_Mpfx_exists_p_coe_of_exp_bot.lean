-- Prove2me | Theorems.Thm_Mpfx_exists_p_coe_of_exp_bot
-- name    : Mpfx.exists_p_coe_of_exp_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:39.279174+00:00
-- url     : https://prove2.me/theorems/44a0ed23-1773-4012-b0b9-5404a503544b
-- title:
--   Mpfx: exists p coe of exp bot
-- statement:
--   A `FiniteFormat` with `exp = ⊥` has finite precision.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L647-L651
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L647-L651

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.exists_p_coe_of_exp_bot {F : FiniteFormat} (he : F.exp = ⊥) :
    ∃ p : ℕ, F.p = (p : Prec) := by sorry
