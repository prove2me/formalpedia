-- Prove2me | Theorems.Thm_Fpy_DigitBound_msb_round_le
-- name    : Fpy.DigitBound.msb_round_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:44.523192+00:00
-- url     : https://prove2.me/theorems/a0e754ff-38e4-4c21-a32f-960684cdad93
-- title:
--   Digit Bound: msb round le
-- statement:
--   A rounding stays below the next power of two at or above the quantum.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L260-L272
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L260-L272

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.msb_round_le {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) (hx : x ≠ 0) {k : ℤ} (hk : F.exp ≤ (k : QExp)) :
    msbOf (.finite (y : ℝ)) ≤ ((max (Int.log 2 |x| + 1) k : ℤ) : EInt) := by sorry
