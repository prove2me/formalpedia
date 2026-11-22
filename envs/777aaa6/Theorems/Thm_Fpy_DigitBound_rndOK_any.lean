-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_any
-- name    : Fpy.DigitBound.rndOK_any
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:52.628469+00:00
-- url     : https://prove2.me/theorems/a88b2f3f-3cfe-4deb-81dc-34eb7c8fee2d
-- title:
--   Digit Bound: rnd OK any
-- statement:
--   All other contexts, including `R`: `[l, μ]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L377-L391
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L377-L391

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

theorem Fpy.DigitBound.rndOK_any (hl : l.Below n) (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : ∀ ι C r, (∀ K ∈ κ, K.Admits ι C) → C.rnd (fpy decode) = some r →
      r = id ∨ ∃ c : RoundCtx, r = c.round ∧ ImagesIn c (Lo.eval ι) (Ho.eval ι)) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min l Lo) (.max (.const ⊤) Ho) ⟨hl.mono (Nat.le_succ n), hLo.mono (Nat.le_succ n)⟩
        ⟨trivial, hHo⟩)
      (.var (n + 1)) (.var n) := by sorry
