-- Prove2me | Theorems.Thm_Fpy_DigitBound_lsb_round
-- name    : Fpy.DigitBound.lsb_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:21.679307+00:00
-- url     : https://prove2.me/theorems/30bf5d67-940f-4ce8-b3b3-eed893826a27
-- title:
--   Digit Bound: lsb round
-- statement:
--   The Digit Bound construction uses the lsb round property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L248-L252
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L248-L252

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.lsb_round {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) : lsbOf (.finite x) ≤ lsbOf (.finite (y : ℝ)) := by sorry
