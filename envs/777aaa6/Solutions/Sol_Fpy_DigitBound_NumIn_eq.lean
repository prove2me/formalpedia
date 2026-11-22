-- Prove2me | solution 1 for Fpy.DigitBound.NumIn.eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:16:20.622584+00:00
-- url     : https://prove2.me/submissions/772551b7-dc6b-48fc-9066-823fdcf7d404

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)
namespace Fpy.DigitBound
namespace NumIn
theorem _root_.solution {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u)
    (hu : u ≠ nan) : lsbOf u = l.eval ι ∧ msbOf u = m.eval ι :=
  (h.resolve_left hu).imp_right And.left
end NumIn
end Fpy.DigitBound
