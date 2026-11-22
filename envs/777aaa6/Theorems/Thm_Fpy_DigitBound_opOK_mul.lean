-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_mul
-- name    : Fpy.DigitBound.opOK_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:26:55.599475+00:00
-- url     : https://prove2.me/theorems/3995ac13-b0a6-4816-a59a-fd1a40bb4f47
-- title:
--   Digit Bound: op OK mul
-- statement:
--   `x × y : [l₁ + l₂, m₁ + m₂ + 1]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L87-L100
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L87-L100

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_mul (hLo : (Term.add l₁ l₂).Below n)
    (hHi : (Term.add (.add m₁ m₂) (.const (1 : ℤ))).Below n) :
    OpOK .mul [(l₁, m₁, τ₁), (l₂, m₂, τ₂)] n (n + 2)
      (bounds n _ _ (hLo.mono (Nat.le_succ n)) hHi) (.var (n + 1)) (.var n) := by sorry
