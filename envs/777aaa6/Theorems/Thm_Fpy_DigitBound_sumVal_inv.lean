-- Prove2me | Theorems.Thm_Fpy_DigitBound_sumVal_inv
-- name    : Fpy.DigitBound.sumVal_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:54.169794+00:00
-- url     : https://prove2.me/theorems/c74aea82-9f9a-4fca-8a54-ba155b22ad71
-- title:
--   Digit Bound: sum Val inv
-- statement:
--   The invariant at the end of `sum`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L39-L45
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L39-L45

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.sumVal_inv {P : ℕ → Num → Prop} {Q : Num → Prop}
    (hstep : ∀ k s w, P k s → Q w → P (k + 1) (Num.add s w)) (hstart : ∀ u, Q u → P 1 u)
    {us : List Num} (hL : 1 ≤ us.length) (hus : ∀ u ∈ us, Q u) : P us.length (sumVal id us) := by sorry
