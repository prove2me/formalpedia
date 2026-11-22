-- Prove2me | Theorems.Thm_Fpy_DigitBound_max_succ_eval
-- name    : Fpy.DigitBound.max_succ_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:47.041186+00:00
-- url     : https://prove2.me/theorems/eca16356-97f0-4e42-950d-fa5c5c729525
-- title:
--   Digit Bound: max succ eval
-- statement:
--   `max(m + 1, τ)` at a finite `m`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L314-L316
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L314-L316

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

theorem Fpy.DigitBound.max_succ_eval {t : Term} {ι : Asgn} {M k : ℤ} (hm : m.eval ι = M) (ht : t.eval ι = k) :
    (Term.max (.add m (.const (1 : ℤ))) t).eval ι = ((max (M + 1) k : ℤ) : EInt) := by sorry
