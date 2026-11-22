-- Prove2me | solution 1 for Mpfx.OverflowMap.ieee_toZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:36:06.507528+00:00
-- url     : https://prove2.me/submissions/d2ef1406-e30c-46df-baf4-7554dceca132

import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Special

set_option autoImplicit true
open Mpfx
open Mpfx.OverflowMap
namespace Mpfx.OverflowMap
theorem _root_.solution (F : FiniteFormat) (hb : F.b ≠ ⊤) (hinf) :
    OverflowMap.ieee F .toZero hb hinf = OverflowMap.saturate F hb := rfl
end Mpfx.OverflowMap
