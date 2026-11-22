-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_logb
-- name    : Fpy.DigitBound.opOK_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:24.679566+00:00
-- url     : https://prove2.me/theorems/5cb733b1-64e4-43c3-824d-b4ea657ef2a6
-- title:
--   Digit Bound: op OK logb
-- statement:
--   `logb(x) : [0, μ]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L149-L156
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L149-L156

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_logb :
    OpOK .logb [(l, m, τ)] n (n + 2) (bounds n (.const (0 : ℤ)) (.const ⊤) trivial trivial)
      (.var (n + 1)) (.var n) := by sorry
