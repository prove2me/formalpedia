-- Prove2me | Theorems.Thm_Fpy_DigitBound_opOK_any
-- name    : Fpy.DigitBound.opOK_any
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:27.151949+00:00
-- url     : https://prove2.me/theorems/4e94f887-41ca-4c91-b516-731b83d6780b
-- title:
--   Digit Bound: op OK any
-- statement:
--   All other operators: `[λ, μ]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L159-L162
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L159-L162

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.opOK_any {op : ArithOp} {Is : List (Term × Term × Option Term)} :
    OpOK op Is n (n + 2) (bounds n (.const ⊥) (.const ⊤) trivial trivial) (.var (n + 1))
      (.var n) := by sorry
