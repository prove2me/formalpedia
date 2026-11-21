-- Prove2me | solution 1 for Mpfx.WithSpecial.neg_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:21:35.423305+00:00
-- url     : https://prove2.me/submissions/b6190c91-5ef0-41f9-95c3-8be5bcbb7d79

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace WithSpecial
theorem _root_.solution {α : Type} [Neg α] (s : Special) :
    (WithSpecial.special s : WithSpecial α).neg = .special s.neg := rfl
end WithSpecial
end Mpfx
