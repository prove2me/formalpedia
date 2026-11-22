-- Prove2me | Theorems.Thm_Fpy_DigitBound_DescribesFields_lookup
-- name    : Fpy.DigitBound.DescribesFields.lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:58.138262+00:00
-- url     : https://prove2.me/theorems/1bc2dbff-383f-4acf-9485-2b79ad30bb34
-- title:
--   Describes Fields: lookup
-- statement:
--   The Describes Fields construction uses the lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L470-L482
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L470-L482

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.DescribesFields.lookup {Ψ : List Con} {ι : Asgn} {l : Label} {a : DVal}
    {v : Val} :
    ∀ {afs : List (Label × DVal)} {fs : List (Label × Val)}, DescribesFields Ψ ι afs fs →
      afs.lookup l = some a → fs.lookup l = some v → Describes Ψ ι a v
  := by sorry
