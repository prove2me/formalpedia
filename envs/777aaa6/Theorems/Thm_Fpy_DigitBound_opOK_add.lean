-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_add
-- name    : Fpy.DigitBound.opOK_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:02.729958+00:00
-- url     : https://prove2.me/theorems/e4ec5c02-26e1-4899-848f-40f04e67c94e
-- title:
--   Digit Bound: op OK add
-- statement:
--   `x ± y : [min(l₁, l₂), max(m₁, m₂) + 1]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L68-L84
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L68-L84

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_add {op : ArithOp} (hop : op = .add ∨ op = .sub) (hLo : (Term.min l₁ l₂).Below n)
    (hHi : (Term.add (.max m₁ m₂) (.const (1 : ℤ))).Below n) :
    OpOK op [(l₁, m₁, τ₁), (l₂, m₂, τ₂)] n (n + 2)
      (bounds n _ _ (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1)) (.var n) := by sorry
