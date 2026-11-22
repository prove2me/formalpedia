-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_fixed
-- name    : Fpy.DigitBound.rndOK_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:33.532813+00:00
-- url     : https://prove2.me/theorems/ebd218a9-07a1-49f5-9424-633032cc05b0
-- title:
--   Digit Bound: rnd OK fixed
-- statement:
--   `Fixed(τ, rm) : [max(l, τ), max(m + 1, τ)]`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L319-L334
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L319-L334

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

theorem Fpy.DigitBound.rndOK_fixed {t : Term} (hl : l.Below n) (ht : t.Below n) (hm : m.Below n)
    (hLo : Lo.Below n) (hHo : Ho.Below n) (hκ : Decodes decode κ (QuantumIs t) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l t) Lo) (.max (.max (.add m (.const (1 : ℤ))) t) Ho)
        ⟨⟨hl.mono (Nat.le_succ n), ht.mono (Nat.le_succ n)⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨⟨⟨hm, trivial⟩, ht⟩, hHo⟩)
      (.var (n + 1)) (.var n) := by sorry
