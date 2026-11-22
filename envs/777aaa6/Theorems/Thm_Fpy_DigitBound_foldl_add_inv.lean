-- Prove2me | Theorems.Thm_Fpy_DigitBound_foldl_add_inv
-- name    : Fpy.DigitBound.foldl_add_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:33.01749+00:00
-- url     : https://prove2.me/theorems/583e8eee-b74e-4a8a-a9cf-178d76319cf2
-- title:
--   Digit Bound: foldl add inv
-- statement:
--   An invariant of `sum`'s additions, indexed by the number of terms.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L28-L36
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sum.lean#L28-L36

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_DigitBound_Sum
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.foldl_add_inv {P : ℕ → Num → Prop} {Q : Num → Prop}
    (hstep : ∀ k s w, P k s → Q w → P (k + 1) (Num.add s w)) :
    ∀ (ws : List Num) (k : ℕ) (s : Num), P k s → (∀ w ∈ ws, Q w) →
      P (k + ws.length) (ws.foldl (fun s w => id (Num.add s w)) s)
  := by sorry
