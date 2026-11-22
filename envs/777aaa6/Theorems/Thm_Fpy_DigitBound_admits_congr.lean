-- Prove2me | Theorems.Thm_Fpy_DigitBound_admits_congr
-- name    : Fpy.DigitBound.admits_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:03.972084+00:00
-- url     : https://prove2.me/theorems/7b7fd3a9-194e-48aa-8111-e3c3d2e2dc02
-- title:
--   Digit Bound: admits congr
-- statement:
--   The Digit Bound construction uses the admits congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L121-L123
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L121-L123

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.admits_congr {n : ℕ} {ι ι' : Asgn} (h : Agree n ι ι') {κ : Option SCtx} {C : Val}
    (hκ : CtxBelow n κ) (hC : ∀ K ∈ κ, K.Admits ι C) : ∀ K ∈ κ, K.Admits ι' C := by sorry
