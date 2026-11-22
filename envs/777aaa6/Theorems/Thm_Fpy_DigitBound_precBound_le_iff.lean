-- Prove2me | Theorems.Thm_Fpy_DigitBound_precBound_le_iff
-- name    : Fpy.DigitBound.precBound_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:45:22.50082+00:00
-- url     : https://prove2.me/theorems/dae21edb-53af-4e8a-9e25-6bd78c8a88cb
-- title:
--   Digit Bound: prec Bound le iff
-- statement:
--   The query: `precBound Ψ l m ≤ p` exactly when every model of `Ψ`'s encoding
--   where `m` is finite satisfies the encoded `m − l + 1 ≤ p`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L204-L213
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L204-L213

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.precBound_le_iff (Ψ : List Con) (l m : Term) (p : ℤ) :
    precBound Ψ l m ≤ p ↔ ∀ M : IModel, (∀ φ ∈ encode Ψ, φ.holds M) →
      m.enc.bot.holds M = false → m.enc.top.holds M = false →
      (Atom.enc ⟨l.width m, .const p⟩).holds M := by sorry
