-- Prove2me | Theorems.Thm_Fpy_DigitBound_DescribesAll_mem
-- name    : Fpy.DigitBound.DescribesAll.mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:19:51.686648+00:00
-- url     : https://prove2.me/theorems/89fcc453-1bb3-403d-867d-84a5e769418c
-- title:
--   Describes All: mem
-- statement:
--   The Describes All construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L497-L502
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L497-L502

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.DescribesAll.mem {Ψ : List Con} {ι : Asgn} {d : DVal} {a : ℕ} :
    ∀ {vs : List Val}, DescribesAll Ψ ι d a vs → ∀ {v : Val}, v ∈ vs →
      ∃ ι₀, Agree a ι ι₀ ∧ Sat ι₀ Ψ ∧ Describes Ψ ι₀ d v
  := by sorry
