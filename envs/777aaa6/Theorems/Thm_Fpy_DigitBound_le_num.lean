-- Prove2me | Theorems.Thm_Fpy_DigitBound_le_num
-- name    : Fpy.DigitBound.le_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:26:15.703966+00:00
-- url     : https://prove2.me/theorems/24ec2901-a236-4f06-b7b0-15261f65473d
-- title:
--   Digit Bound: le num
-- statement:
--   A number in `[l, m]` lies in a fresh interval `[n + 1, n]` bounded by `Lo ≤ l`
--   and `m ≤ Hi`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L19-L30
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L19-L30

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.le_num {Ψg : List Con} {n : ℕ} {l m Lo Hi : Term} {τ : Option Term} (hLo : Lo.Below n)
    (hHi : Hi.Below n) (hl : ∀ ι, Lo.eval ι ≤ l.eval ι) (hm : ∀ ι, m.eval ι ≤ Hi.eval ι) :
    DVal.Le n (n + 2) Ψg (bounds n Lo Hi (hLo.mono (Nat.le_succ n)) hHi) (.num l m τ)
      (.num (.var (n + 1)) (.var n) none) := by sorry
