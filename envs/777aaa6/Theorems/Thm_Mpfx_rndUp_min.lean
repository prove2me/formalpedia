-- Prove2me | Theorems.Thm_Mpfx_rndUp_min
-- name    : Mpfx.rndUp_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:46:34.438182+00:00
-- url     : https://prove2.me/theorems/b97a83cc-2b00-41f6-9139-b69977f90eb2
-- title:
--   Mpfx: rnd Up min
-- statement:
--   The Mpfx construction uses the rnd Up min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L131-L133
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L131-L133

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndUp_min (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz : z ∈ F.unbounded) (hxz : x ≤ (z : ℝ)) : (rndUp F x : ℝ) ≤ (z : ℝ) := by sorry
