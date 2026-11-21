-- Prove2me | solution 1 for Mpfx.rnd_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:45:08.410572+00:00
-- url     : https://prove2.me/submissions/bb41ee07-951f-4c27-9f04-267f9db11318

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op

set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (S : SpecialMap F.toFormat)
    (O : OverflowMap F.toFormat) (rm : RoundingMode) (s : Special) :
    rnd F S O rm (.special s) = .value (S.map s) := rfl
end Mpfx
