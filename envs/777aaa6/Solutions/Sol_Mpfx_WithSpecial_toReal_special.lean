-- Prove2me | solution 1 for Mpfx.WithSpecial.toReal_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:21:43.645944+00:00
-- url     : https://prove2.me/submissions/72d9d988-7323-4e21-9f09-db9e6d9320c9

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace WithSpecial
theorem _root_.solution (s : Special) :
    (WithSpecial.special s : WithSpecial Dyadic).toReal = .special s := rfl
end WithSpecial
end Mpfx
