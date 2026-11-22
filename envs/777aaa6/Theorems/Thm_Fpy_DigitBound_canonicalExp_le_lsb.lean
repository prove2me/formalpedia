-- Prove2me | Theorems.Thm_Fpy_DigitBound_canonicalExp_le_lsb
-- name    : Fpy.DigitBound.canonicalExp_le_lsb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:36.586141+00:00
-- url     : https://prove2.me/theorems/c09c363e-7329-4734-900e-be99264806c7
-- title:
--   Digit Bound: canonical Exp le lsb
-- statement:
--   The Digit Bound construction uses the canonical Exp le lsb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L254-L257
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L254-L257

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}

theorem Fpy.DigitBound.canonicalExp_le_lsb {F : FiniteFormat} {rm : RoundingMode} {x : ℝ} {y : Mpfx.Dyadic}
    (hy : RoundsFinite F.unbounded rm x y) :
    ((F.canonicalExp x : ℤ) : EInt) ≤ lsbOf (.finite (y : ℝ)) := by sorry
