-- Prove2me | solution 1 for Mpfx.WithSpecial.toReal_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:21:39.103585+00:00
-- url     : https://prove2.me/submissions/40d6f21d-b67b-4012-8b87-867d007208ed

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace WithSpecial
theorem _root_.solution (d : Dyadic) :
    (WithSpecial.finite d).toReal = .finite (d : ℝ) := rfl
end WithSpecial
end Mpfx
