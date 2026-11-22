-- Prove2me | solution 1 for Fpy.DigitBound.NumIn.term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:19:02.80919+00:00
-- url     : https://prove2.me/submissions/80441783-0a77-49b1-bd66-2320e4092b8f

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace NumIn
theorem _root_.solution {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m (some t) u) :
    u = nan ∨ u = numOfE (t.eval ι) :=
  h.imp_right fun ⟨_, _, ht⟩ => ht t rfl
end NumIn
end Fpy.DigitBound
