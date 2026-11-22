-- Prove2me | solution 1 for Fpy.DigitBound.NumIn.withTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:23:34.732909+00:00
-- url     : https://prove2.me/submissions/5410c59d-cf35-435c-9374-4fda494ed382

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace NumIn
theorem _root_.solution {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m none u)
    (ht : u = nan ∨ u = numOfE (t.eval ι)) : NumIn ι l m (some t) u := by
  rcases h with h | ⟨hl, hm, -⟩
  · exact .inl h
  · rcases ht with ht | ht
    · exact .inl ht
    · exact .inr ⟨hl, hm, fun t' ht' => by cases ht'; exact ht⟩
end NumIn
end Fpy.DigitBound
