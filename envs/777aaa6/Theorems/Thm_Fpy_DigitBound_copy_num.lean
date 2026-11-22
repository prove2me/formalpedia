-- Prove2me | Theorems.Thm_Fpy_DigitBound_copy_num
-- name    : Fpy.DigitBound.copy_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:25:32.776833+00:00
-- url     : https://prove2.me/theorems/13a757fd-31dc-4d09-abce-b63f660b1442
-- title:
--   Digit Bound: copy num
-- statement:
--   **D-Index's copy** of a numeric element: its variables `[a, b)` renamed to
--   `[n, n + (b − a))`, with the constraints of `Ψg` on them copied.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L120-L151
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L120-L151

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.copy_num {Ψg : List Con} {a b n : ℕ} {l m : Term} {τ : Option Term} (hab : a ≤ b)
    (hbn : b ≤ n) (hl : l.Below b) (hm : m.Below b) (hτ : ∀ t ∈ τ, t.Below b) :
    DVal.Copy n (n + (b - a)) Ψg (copyCons Ψg a b n (hab.trans hbn)) (.num l m τ) a
      (.num (l.rename (shift a b n)) (m.rename (shift a b n))
        (τ.map (Term.rename (shift a b n)))) := by sorry
