-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_exp2
-- name    : Fpy.DigitBound.opOK_exp2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:10.262616+00:00
-- url     : https://prove2.me/theorems/6146802b-d458-40df-8040-99d34f86b55e
-- title:
--   Digit Bound: op OK exp2
-- statement:
--   `2ˣ : [τ, τ]` when `x` has term `τ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L137-L146
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L137-L146

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_exp2 {t : Term} (hLo : t.Below n) :
    OpOK .exp2 [(l, m, some t)] n (n + 2) (bounds n t t (hLo.mono (Nat.le_succ n)) hLo)
      (.var (n + 1)) (.var n) := by sorry
