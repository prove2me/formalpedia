-- Prove2me | solution 1 for Fpy.boundOK_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:33:10.744383+00:00
-- url     : https://prove2.me/submissions/7b5259c2-b2e3-4791-a0f3-decf42c12106

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower

set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution (d : Mpfx.Dyadic) : Format.boundOK ⊤ d := trivial
end Fpy
