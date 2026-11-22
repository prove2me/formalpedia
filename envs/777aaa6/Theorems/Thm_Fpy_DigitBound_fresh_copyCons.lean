-- Prove2me | Theorems.Thm_Fpy_DigitBound_fresh_copyCons
-- name    : Fpy.DigitBound.fresh_copyCons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:25:23.877686+00:00
-- url     : https://prove2.me/theorems/508ee29d-46c1-4cb2-8437-c85bd0fc077b
-- title:
--   Digit Bound: fresh copy Cons
-- statement:
--   The Digit Bound construction uses the fresh copy Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L96-L116
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L96-L116

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.fresh_copyCons {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∀ {Ψ : List Con}, (Ψ.map Con.head).Nodup →
      Fresh n (n + (b - a)) (copyCons Ψ a b n (hab.trans hbn)) := by sorry
