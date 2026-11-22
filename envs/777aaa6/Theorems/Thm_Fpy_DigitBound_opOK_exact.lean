-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_exact
-- name    : Fpy.DigitBound.opOK_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:06.11212+00:00
-- url     : https://prove2.me/theorems/4b3b3042-8659-48b9-a6ba-5e6af27bb54f
-- title:
--   Digit Bound: op OK exact
-- statement:
--   `−x`, `|x|`, `round(x)`, `cast(x)` keep `[l, m]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L103-L116
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L103-L116

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_exact {op : ArithOp} (hop : op = .neg ∨ op = .abs ∨ op = .round ∨ op = .cast) :
    OpOK op [(l, m, τ)] n n [] l m := by sorry
