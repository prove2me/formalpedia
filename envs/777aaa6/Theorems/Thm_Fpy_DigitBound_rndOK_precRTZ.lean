-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_precRTZ
-- name    : Fpy.DigitBound.rndOK_precRTZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:46.867188+00:00
-- url     : https://prove2.me/theorems/f7c507b0-9b27-4d0d-9b78-61b38ca91368
-- title:
--   Digit Bound: rnd OK prec RTZ
-- statement:
--   `IEEE754(es, nb, RTZ) : [max(l, m − p + 1), m]`, for precision `p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L337-L353
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L337-L353

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

theorem Fpy.DigitBound.rndOK_precRTZ {p : ℕ} (hl : l.Below n) (hm : m.Below n) (hLo : Lo.Below n)
    (hHo : Ho.Below n) (hκ : Decodes decode κ (fun _ c => c.F.p = p ∧ c.rm = .toZero) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l (.add m (.const (1 - p : ℤ)))) Lo) (.max m Ho)
        ⟨⟨hl.mono (Nat.le_succ n), hm.mono (Nat.le_succ n), trivial⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨hm, hHo⟩)
      (.var (n + 1)) (.var n) := by sorry
