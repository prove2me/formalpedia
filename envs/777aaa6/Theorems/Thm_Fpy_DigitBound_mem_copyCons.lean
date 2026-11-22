-- Prove2me | Theorems.Thm_Fpy_DigitBound_mem_copyCons
-- name    : Fpy.DigitBound.mem_copyCons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:20:11.122553+00:00
-- url     : https://prove2.me/theorems/5645211c-cf13-4864-85bd-1d68ac17edf0
-- title:
--   Digit Bound: mem copy Cons
-- statement:
--   The Digit Bound construction uses the mem copy Cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L89-L94
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L89-L94

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.mem_copyCons {Ψ : List Con} {a b n : ℕ} {han : a ≤ n} {c' : Con}
    (h : c' ∈ copyCons Ψ a b n han) :
    ∃ c ∈ Ψ, ∃ hc : a ≤ c.head ∧ c.head < b, c' = c.copy a b n hc han := by sorry
