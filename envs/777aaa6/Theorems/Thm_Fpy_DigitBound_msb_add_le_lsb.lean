-- Prove2me | Theorems.Thm_Fpy_DigitBound_msb_add_le_lsb
-- name    : Fpy.DigitBound.msb_add_le_lsb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:23:17.296665+00:00
-- url     : https://prove2.me/theorems/55a6d803-d1bd-4eb6-9b1d-83153761629b
-- title:
--   Digit Bound: msb add le lsb
-- statement:
--   A value of precision `p` has its digits within `p` positions.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L275-L287
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L275-L287

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.msb_add_le_lsb {F : FiniteFormat} {p : ℕ} (hp : F.p = p) {y : Mpfx.Dyadic}
    (hy : y ∈ F.unbounded) (h0 : (y : ℝ) ≠ 0) :
    msbOf (.finite (y : ℝ)) + ((1 - p : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) := by sorry
