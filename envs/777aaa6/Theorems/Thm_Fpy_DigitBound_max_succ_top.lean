-- Prove2me | Theorems.Thm_Fpy_DigitBound_max_succ_top
-- name    : Fpy.DigitBound.max_succ_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:58.191501+00:00
-- url     : https://prove2.me/theorems/803acd0f-2529-47c8-8cc9-83c36fb1a961
-- title:
--   Digit Bound: max succ top
-- statement:
--   `max(m + 1, τ)` is `⊤` at `m = ⊤`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L308-L311
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L308-L311

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Fpy_DigitBound_Table
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {decode : List (Label × Val) → Option RoundCtx}
variable {n : ℕ} {l m l₁ m₁ l₂ m₂ : Term} {τ τ₁ τ₂ : Option Term}
variable {κ : Option SCtx} {Lo Ho : Term}

theorem Fpy.DigitBound.max_succ_top {t : Term} (ι : Asgn) (h : m.eval ι = ⊤) :
    (Term.max (.add m (.const (1 : ℤ))) t).eval ι = ⊤ := by sorry
