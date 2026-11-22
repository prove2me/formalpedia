-- Prove2me | Theorems.Thm_Fpy_DigitBound_rndOK_prec
-- name    : Fpy.DigitBound.rndOK_prec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:27:43.439543+00:00
-- url     : https://prove2.me/theorems/6db7ce18-ef7e-4f87-8d34-edbfd29dbae7
-- title:
--   Digit Bound: rnd OK prec
-- statement:
--   `IEEE754(es, nb, rm) : [max(l, μ − p + 1), μ]` with `μ ≤ max(m + 1, τ)`, for
--   precision `p` and quantum `2^τ`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L357-L374
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Table.lean#L357-L374

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

theorem Fpy.DigitBound.rndOK_prec {p : ℕ} {t : Term} (hl : l.Below n) (ht : t.Below n) (hm : m.Below n)
    (hLo : Lo.Below n) (hHo : Ho.Below n)
    (hκ : Decodes decode κ (fun ι c => c.F.p = p ∧ QuantumIs t ι c) Lo Ho) :
    RndOK decode κ l m n (n + 2)
      (bounds n (.min (.max l (.add (.var n) (.const (1 - p : ℤ)))) Lo)
        (.max (.max (.add m (.const (1 : ℤ))) t) Ho)
        ⟨⟨hl.mono (Nat.le_succ n), Nat.lt_succ_self n, trivial⟩, hLo.mono (Nat.le_succ n)⟩
        ⟨⟨⟨hm, trivial⟩, ht⟩, hHo⟩)
      (.var (n + 1)) (.var n) := by sorry
