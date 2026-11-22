-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_real
-- name    : Fpy.DigitBound.rndOK_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:28.712161+00:00
-- url     : https://prove2.me/theorems/083ee66a-cf4f-4543-b2b1-ccf67eccc485
-- title:
--   Digit Bound: rnd OK real
-- statement:
--   `R`: `[l, m]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L183-L187
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L183-L187

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.rndOK_real : RndOK decode (some .real) l m n n [] l m := by sorry
