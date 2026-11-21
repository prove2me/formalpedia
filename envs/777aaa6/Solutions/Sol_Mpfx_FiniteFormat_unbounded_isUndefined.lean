-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_isUndefined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:41:42.526919+00:00
-- url     : https://prove2.me/submissions/77bbeffc-af8c-423b-baad-20caf25fb4b3

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace FiniteFormat
theorem _root_.solution (F : FiniteFormat)
    (rm : RoundingMode) :
    F.unbounded.IsUndefined rm = F.IsUndefined rm := rfl
end FiniteFormat
end Mpfx
